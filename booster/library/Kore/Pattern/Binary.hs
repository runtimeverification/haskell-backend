{-# LANGUAGE PatternSynonyms #-}

module Kore.Pattern.Binary (decodeKorePattern, test) where

import Control.Monad (unless)
import Control.Monad.Extra (forM)
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT), asks)
import Control.Monad.Trans.State (StateT, evalStateT, gets, modify)
import Data.Binary.Get (
    Get,
    bytesRead,
    getByteString,
    getInt16le,
    getWord8,
    isEmpty,
    runGet,
 )
import Data.Bits (Bits (complement, shiftL, (.&.), (.|.)))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.Int (Int16)
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word64)
import GHC.Word (Word8)
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Syntax.ParsedKore

pattern KORECompositePattern, KOREStringPattern, KORECompositeSort, KORESortVariable, KORESymbol, KOREVariablePattern, KOREVariable :: Word8
pattern KORECompositePattern = 0x4
pattern KOREStringPattern = 0x5
pattern KORECompositeSort = 0x6
pattern KORESortVariable = 0x7
pattern KORESymbol = 0x8
pattern KOREVariablePattern = 0x9
pattern KOREVariable = 0xD

data Version = Version
    { major :: Int16
    , minor :: Int16
    , patch :: Int16
    }
    deriving (Show)

data DecoderState = DecoderState
    { internedStrings :: Map.Map Int BS.ByteString
    , currentSymbolWithSorts :: Maybe (Symbol, [Sort])
    , sortStack :: [Sort]
    , termOrTextStack :: [Either Text.Text Term]
    }
    deriving (Show)

newtype DecodeM a = DecodeM {unDecodeM :: ReaderT (Version, KoreDefinition) (StateT DecoderState Get) a}
    deriving newtype (Functor, Applicative, Monad, MonadFail)

runDecodeM :: Version -> KoreDefinition -> DecodeM a -> Get a
runDecodeM v def = flip evalStateT (DecoderState mempty Nothing mempty mempty) . flip runReaderT (v, def) . unDecodeM

liftDecode :: Get a -> DecodeM a
liftDecode m = DecodeM $ lift $ lift m

askVersion :: DecodeM Version
askVersion = DecodeM $ asks fst

getInternedStrings :: DecodeM (Map.Map Int BS.ByteString)
getInternedStrings = DecodeM $ lift $ gets internedStrings

insertInternedString :: Int -> BS.ByteString -> DecodeM ()
insertInternedString pos str =
    DecodeM $
        lift $
            modify (\s@DecoderState{internedStrings} -> s{internedStrings = Map.insert pos str internedStrings})

areCompatible :: Version -> Version -> Bool
areCompatible a b = a.major == b.major && a.minor == b.minor

decodeMagicHeaderAndVersion :: Get Version
decodeMagicHeaderAndVersion = do
    _ <- getWord8
    header <- getByteString 4
    unless (header == "KORE") $ fail "Invalid magic header for binary KORE"
    Version <$> getInt16le <*> getInt16le <*> getInt16le

decodeLength :: Int -> DecodeM Int
decodeLength l = do
    version <- askVersion
    liftDecode $
        if areCompatible version $ Version 1 0 0
            then readAndShift l 0x0
            else readAndShiftV2 True 0 0
  where
    readAndShift :: Int -> Int -> Get Int
    readAndShift counter ret
        | counter > 0 = do
            r <- getWord8
            readAndShift (counter - 1) $ (ret `shiftL` 8) .|. fromIntegral r
        | otherwise = pure ret

    readAndShiftV2 :: Bool -> Int -> Int -> Get Int
    readAndShiftV2 _ steps _ | steps >= 9 = fail "No terminating byte in variable-length field"
    readAndShiftV2 False _ ret = pure ret
    readAndShiftV2 True steps ret = do
        chunk <- getWord8
        let contBit = 0x80
            continue = chunk .&. contBit == 0x1
            chunk' = chunk .&. complement contBit
            ret' = ret .|. (fromIntegral $ (fromIntegral chunk' :: Word64) `shiftL` (7 * steps))
        readAndShiftV2 continue (steps + 1) ret'

decodeString :: DecodeM BS.ByteString
decodeString =
    liftDecode getWord8 >>= \case
        0x1 -> do
            position <- fromIntegral <$> liftDecode bytesRead
            len <- decodeLength 4
            str <- liftDecode $ getByteString len
            insertInternedString position str
            pure str
        0x2 -> do
            position <- fromIntegral <$> liftDecode bytesRead
            backref <- decodeLength 4
            m <- getInternedStrings
            case Map.lookup (position - backref + 1) m of
                Just str -> do
                    insertInternedString position str
                    pure str
                Nothing -> fail "Incorrect offset for interned string"
        _ -> fail "Incorrect String encoding"

popTermOrTextStack :: Int -> DecodeM [Either Text.Text Term]
popTermOrTextStack n = DecodeM $ lift $ do
    stack <- gets termOrTextStack
    unless (length stack >= n) $ fail "Trying to pop more items off the stack than available"
    modify (\s -> s{termOrTextStack = drop n stack})
    pure $ reverse $ take n stack

pushTermOrTextStack :: Either Text.Text Term -> DecodeM ()
pushTermOrTextStack t = DecodeM $ lift $ do
    modify (\s@DecoderState{termOrTextStack} -> s{termOrTextStack = t : termOrTextStack})

popSortStack :: Int -> DecodeM [Sort]
popSortStack n = DecodeM $ lift $ do
    stack <- gets sortStack
    unless (length stack >= n) $ fail "Trying to pop more items off the stack than available"
    modify (\s -> s{sortStack = drop n stack})
    pure $ reverse $ take n stack

pushSortStack :: Sort -> DecodeM ()
pushSortStack sort = DecodeM $ lift $ do
    modify (\s@DecoderState{sortStack} -> s{sortStack = sort : sortStack})

getCurrentSymbolWithSorts :: DecodeM (Maybe (Symbol, [Sort]))
getCurrentSymbolWithSorts = DecodeM $ lift $ gets currentSymbolWithSorts

setCurrentSymbolWithSorts :: (Symbol, [Sort]) -> DecodeM ()
setCurrentSymbolWithSorts symbolWithSorts = DecodeM $ lift $ do
    modify (\s -> s{currentSymbolWithSorts = Just symbolWithSorts})

lookupKoreDefinitionSymbol :: SymbolName -> DecodeM (Maybe Symbol)
lookupKoreDefinitionSymbol name = DecodeM $ asks (Map.lookup name . symbols . snd)

decodeBlock :: DecodeM Term
decodeBlock = do
    whileNotEmpty $ do
        liftDecode getWord8 >>= \case
            KORECompositePattern ->
                getCurrentSymbolWithSorts >>= \case
                    Just symbolAndSorts -> do
                        arity <- decodeLength 2
                        args <- popTermOrTextStack arity
                        mkSymbolApplication symbolAndSorts args >>= pushTermOrTextStack
                    Nothing -> fail "No current symbol set"
            KOREStringPattern -> do
                str <- decodeString
                pushTermOrTextStack $ Left $ Text.decodeUtf8 str
            KORECompositeSort -> do
                arity <- decodeLength 2
                sortName <- decodeString
                args <- popSortStack arity
                pushSortStack $ SortApp (Text.decodeUtf8 sortName) args
            KORESortVariable -> fail "KORESortVariable decoding undefined"
            KORESymbol -> do
                arity <- decodeLength 2
                symbolName <- decodeString
                args <- popSortStack arity
                mkSymbolWithSorts (Text.decodeUtf8 symbolName) args >>= setCurrentSymbolWithSorts
            KOREVariablePattern -> fail "KOREVariablePattern decoding undefined"
            KOREVariable -> fail "KOREVariable decoding undefined"
            _ -> fail "Invalid header"

    popTermOrTextStack 1 >>= \case
        [Right trm] -> pure trm
        _ -> fail "Expecting a term on the top of the stack"
  where
    whileNotEmpty m =
        liftDecode isEmpty >>= \case
            True -> pure ()
            False -> m >> whileNotEmpty m

    mkSymbolApplication (DV sort, _) [Left txt] = pure $ Right $ DomainValue sort txt
    mkSymbolApplication (symbol, sorts) xs = do
        args <- forM xs $ \case
            Left _txt -> fail "Expecting term"
            Right trm -> pure trm
        pure $ Right $ SymbolApplication symbol sorts args

    mkSymbolWithSorts "\\dv" [sort] = pure (Symbol "\\dv" [] [] sort undefined, [])
    mkSymbolWithSorts name sorts =
        lookupKoreDefinitionSymbol name >>= \case
            Just symbol@Symbol{sortVars} -> pure (symbol, zipWith (const id) sortVars sorts)
            Nothing -> fail $ "Unknown symbol " <> show name

decodeKorePattern :: KoreDefinition -> Get Term
decodeKorePattern def = do
    version <- decodeMagicHeaderAndVersion
    runDecodeM version def decodeBlock

test :: FilePath -> Text.Text -> FilePath -> IO Term
test definitionFile mainModuleName f = do
    internalModule <-
        either (error . show) id
            <$> loadDefinition mainModuleName definitionFile
    runGet (decodeKorePattern internalModule) <$> BL.readFile f

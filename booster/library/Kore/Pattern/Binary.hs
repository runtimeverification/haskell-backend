{-# LANGUAGE PatternSynonyms #-}

module Kore.Pattern.Binary (decodeKorePattern, test) where

import Control.Monad (unless)
import Control.Monad.Extra (forM)
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT), ask, asks)
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
import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Syntax.ParsedKore

-- | tags indicating the next element in a block, see @'decodeBlock'@
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

newtype DecodeM a = DecodeM {unDecodeM :: ReaderT (Version, Maybe KoreDefinition) (StateT DecoderState Get) a}
    deriving newtype (Functor, Applicative, Monad, MonadFail)

runDecodeM :: Version -> Maybe KoreDefinition -> DecodeM a -> Get a
runDecodeM v mDef = flip evalStateT (DecoderState mempty Nothing mempty mempty) . flip runReaderT (v, mDef) . unDecodeM

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

{- | Length (non-negative integer) is encoded in one of two special
  formats (depending on the version).
  Version 1.0.x: stored big-endian in a fixed amount of bytes.
  Other versions:
    - stored little-endian using _the lower 7 bits_ of each byte
    - where bit 8 of the byte is set if the number continues. If bit 8
      is _not_ set, the decoding ends.
    - a maximum of 9 bytes is read (max. value is '2^(7 * 9)')
-}
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
            continue = chunk .&. contBit == contBit
            chunk' = chunk .&. complement contBit
            ret' = ret .|. (fromIntegral $ (fromIntegral chunk' :: Word64) `shiftL` (7 * steps))
        readAndShiftV2 continue (steps + 1) ret'

{- | A string can either be a literal encoded as length/contents (tag
  0x01), or a back-reference to a previously-unpacked string (tag
  0x02), given as a _relative_ offset backwards from the current
  position. The previously-unpacked strings are remembered in the
  string table of the decode state to avoid having to step back.
-}
decodeString :: DecodeM BS.ByteString
decodeString = do
    liftDecode getWord8 >>= \case
        0x1 -> do
            -- record the position of the length argument, to be added to the backref map
            position <- fromIntegral <$> liftDecode bytesRead
            len <- decodeLength 4
            str <- liftDecode $ getByteString len
            insertInternedString position str
            pure str
        0x2 -> do
            backref <- decodeLength 4
            -- we look up the position after reading `backref` and subtract `backref` from it,
            -- to obtain the position of the string, which we then look up in the backref map
            position <- fromIntegral <$> liftDecode bytesRead
            m <- getInternedStrings
            case Map.lookup (position - backref) m of
                Just str -> pure str
                Nothing -> do
                    let offsets =
                            [ show n <> " -> " <> show s <> "\n"
                            | (n, s) <- Map.assocs m
                            ]
                    fail $ "Incorrect offset for interned string at " <> show (position, backref) <> " with table\n " <> unwords offsets
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
lookupKoreDefinitionSymbol name = DecodeM $ do
    (_, mDef) <- ask
    pure $ case mDef of
        -- return a symbol with dummy attributes if no definition is supplied.
        -- this should be used for testing ONLY!
        Nothing -> Just $ Symbol name [] [] (SortApp "dummy" []) (SymbolAttributes PartialFunction False False)
        Just def -> Map.lookup name $ symbols def

{- | Successively decodes items from the given "block" of bytes,
  branching on the initial tag of the item.
  A block is a sequence of items which are encoded as described in the
  comments on each tag case below.
  Decoding adds items to an internal stack, symbol application
  consumes stack elements according to the symbol arity. At the end of
  the block, the stack is expected to hold a single element (the
  resulting term which is returned).
-}
decodeBlock :: DecodeM Term
decodeBlock = do
    whileNotEmpty $ do
        liftDecode getWord8 >>= \case
            KORECompositePattern ->
                -- apply node (arity), uses current symbol and the stack of terms
                getCurrentSymbolWithSorts >>= \case
                    Just symbolAndSorts -> do
                        arity <- decodeLength 2
                        args <- popTermOrTextStack arity
                        mkSymbolApplication symbolAndSorts args >>= pushTermOrTextStack
                    Nothing -> fail "No current symbol set"
            KOREStringPattern -> do
                -- either literal string (length,data) or back-reference (rel.offset)
                str <- decodeString
                pushTermOrTextStack $ Left $ Text.decodeUtf8 str
            KORECompositeSort -> do
                -- sort constructor (arity, name)
                arity <- decodeLength 2
                sortName <- decodeString
                args <- popSortStack arity
                pushSortStack $ SortApp (Text.decodeUtf8 sortName) args
            KORESortVariable -> fail "KORESortVariable decoding undefined"
            KORESymbol -> do
                -- symbol applied to (sort) arguments (arity, name)
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

{- | The term in binary format is stored as follows:
Bytes   1    4      2         2         2                ?
      +----+------+---------+---------+---------------+---------+
      | 7f | KORE | <major> | <minor> | <patch-level> | <BLOCK> |
      +----+------+---------+---------+---------------+---------+
with the first byte ignored (7f) a fixed magic header "KORE", major,
minor, patch-level 16-bit integers (little-endian), and the block
encoded as described in @'decodeBlock'@.
https://github.com/runtimeverification/llvm-backend/blob/master/docs/binary_kore.md
-}
decodeKorePattern' :: Maybe KoreDefinition -> Get Term
decodeKorePattern' mDef = do
    version <- decodeMagicHeaderAndVersion
    runDecodeM version mDef decodeBlock

decodeKorePattern :: KoreDefinition -> Get Term
decodeKorePattern = decodeKorePattern' . Just

test :: Maybe (FilePath, Text.Text) -> FilePath -> IO Term
test (Just (definitionFile, mainModuleName)) f = do
    internalModule <-
        either (error . show) id
            <$> loadDefinition mainModuleName definitionFile
    runGet (decodeKorePattern internalModule) <$> BL.readFile f
test Nothing f =
    runGet (decodeKorePattern' Nothing) <$> BL.readFile f

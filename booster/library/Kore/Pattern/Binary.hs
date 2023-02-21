{-# LANGUAGE PatternSynonyms #-}

module Kore.Pattern.Binary (Version (..), Block (..), decodeTerm, decodeTerm', decodePattern, encodeMagicHeaderAndVersion, encodePattern, encodeTerm, test, encodeSingleBlock, decodeSingleBlock) where

import Control.Monad (forM_, unless)
import Control.Monad.Extra (forM)
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT), ask, asks)
import Control.Monad.Trans.State (StateT, evalStateT, gets, modify)
import Data.Binary.Get
import Data.Binary.Put
import Data.Bits (Bits (complement, shiftL, (.&.), (.|.)), shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.Int (Int16)
import Data.List (intercalate)
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Word (Word64)
import GHC.Word (Word8)
import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Pattern.Util (sortOfTerm)
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

data Block
    = BTerm Term
    | BPredicate Predicate
    | BString ByteString
    | BSort Sort
    | BSymbol ByteString [Sort]
    deriving (Show)

data DecoderState = DecoderState
    { internedStrings :: Map.Map Int BS.ByteString
    , stack :: [Block]
    }
    deriving (Show)

newtype DecodeM a = DecodeM {unDecodeM :: ReaderT (Version, Maybe KoreDefinition) (StateT DecoderState Get) a}
    deriving newtype (Functor, Applicative, Monad, MonadFail)

runDecodeM :: Version -> Maybe KoreDefinition -> DecodeM a -> Get a
runDecodeM v mDef = flip evalStateT (DecoderState mempty mempty) . flip runReaderT (v, mDef) . unDecodeM

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
    header <- getByteString 5
    unless (header == "\127KORE") $ fail "Invalid magic header for binary KORE"
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

getStack :: DecodeM [Block]
getStack = DecodeM $ lift $ gets stack

popStack :: Int -> DecodeM [Block]
popStack n = DecodeM $ lift $ do
    stack <- gets stack
    unless (length stack >= n) $ fail "Trying to pop more items off the stack than available"
    modify (\s -> s{stack = drop n stack})
    pure $ reverse $ take n stack

pushStack :: Block -> DecodeM ()
pushStack t = DecodeM $ lift $ do
    modify (\s@DecoderState{stack} -> s{stack = t : stack})

popStackSorts :: Int -> DecodeM [Sort]
popStackSorts n =
    popStack n >>= \stack' -> forM stack' $ \case
        BSort s -> pure s
        _ -> fail "popping a non sort"

lookupKoreDefinitionSymbol :: SymbolName -> DecodeM (Maybe Symbol)
lookupKoreDefinitionSymbol name = DecodeM $ do
    (_, mDef) <- ask
    pure $ case mDef of
        -- return a symbol with dummy attributes if no definition is supplied.
        -- this should be used for testing ONLY!
        Nothing -> Just $ Symbol name [] [] (SortApp "UNKNOWN" []) (SymbolAttributes PartialFunction False False)
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
decodeBlock :: DecodeM [Block]
decodeBlock = do
    whileNotEmpty $ do
        liftDecode getWord8 >>= \case
            KORECompositePattern ->
                -- apply node (arity), uses current symbol and the stack of terms
                popStack 1 >>= \case
                    [BSymbol symbolName sorts] -> do
                        arity <- decodeLength 2
                        args <- popStack arity
                        mkSymbolApplication symbolName sorts args >>= pushStack
                    _ -> fail "No current symbol set"
            KOREStringPattern -> do
                -- either literal string (length,data) or back-reference (rel.offset)
                str <- decodeString
                pushStack $ BString str
            KORECompositeSort -> do
                -- sort constructor (arity, name)
                arity <- decodeLength 2
                sortName <- decodeString
                args <- popStackSorts arity
                pushStack $ BSort $ SortApp sortName args
            KORESortVariable -> do
                var <- decodeString
                pushStack $ BSort $ SortVar var
            KORESymbol -> do
                -- symbol applied to (sort) arguments (arity, name)
                arity <- decodeLength 2
                symbolName <- decodeString
                sorts <- popStackSorts arity
                pushStack $ BSymbol symbolName sorts
            KOREVariablePattern -> pure ()
            KOREVariable -> do
                var <- decodeString
                [sort] <- popStackSorts 1
                pushStack $ BTerm $ Var $ Variable sort var
            h -> fail $ "Invalid header " <> show h

    getStack
  where
    whileNotEmpty m =
        liftDecode isEmpty >>= \case
            True -> pure ()
            False -> m >> whileNotEmpty m

    mkSymbolApplication :: ByteString -> [Sort] -> [Block] -> DecodeM Block
    mkSymbolApplication "\\and" _ [BPredicate p1, BPredicate p2] = pure $ BPredicate $ AndPredicate p1 p2
    mkSymbolApplication "\\and" _ [BTerm t1, BTerm t2] = pure $ BTerm $ AndTerm t1 t2
    mkSymbolApplication "\\and" _ bs =
        argError "AndTerm/AndPredicate" [BTerm undefined, BTerm undefined] bs
    mkSymbolApplication "\\bottom" _ [] = pure $ BPredicate Bottom
    mkSymbolApplication "\\bottom" _ bs = argError "Bottom" [] bs
    mkSymbolApplication "\\ceil" _ [BTerm t] = pure $ BPredicate $ Ceil t
    mkSymbolApplication "\\ceil" _ bs = argError "Ceil" [BTerm undefined] bs
    mkSymbolApplication "\\dv" [sort] [BString txt] = pure $ BTerm $ DomainValue sort txt
    mkSymbolApplication "\\dv" _ bs = argError "DomainValue" [BString undefined] bs
    mkSymbolApplication "\\equals" _ [BTerm t1, BTerm t2] = pure $ BPredicate $ EqualsTerm t1 t2
    mkSymbolApplication "\\equals" _ [BPredicate p1, BPredicate p2] = pure $ BPredicate $ EqualsPredicate p1 p2
    mkSymbolApplication "\\equals" _ bs =
        argError "EqualBTerm/EqualBPredicate" [BTerm undefined, BTerm undefined] bs
    mkSymbolApplication "\\exists" _ [BTerm (Var (Variable _ var)), BPredicate p] = pure $ BPredicate $ Exists var p
    mkSymbolApplication "\\exists" _ bs = argError "Exists" [BTerm undefined, BPredicate undefined] bs
    mkSymbolApplication "\\forall" _ [BTerm (Var (Variable _ var)), BPredicate p] = pure $ BPredicate $ Forall var p
    mkSymbolApplication "\\forall" _ bs = argError "Forall" [BTerm undefined, BPredicate undefined] bs
    mkSymbolApplication "\\iff" _ [BPredicate p1, BPredicate p2] = pure $ BPredicate $ Iff p1 p2
    mkSymbolApplication "\\iff" _ bs = argError "Iff" [BPredicate undefined, BPredicate undefined] bs
    mkSymbolApplication "\\implies" _ [BPredicate p1, BPredicate p2] = pure $ BPredicate $ Implies p1 p2
    mkSymbolApplication "\\implies" _ bs = argError "Implies" [BPredicate undefined, BPredicate undefined] bs
    mkSymbolApplication "\\in" _ [BTerm t1, BTerm t2] = pure $ BPredicate $ In t1 t2
    mkSymbolApplication "\\in" _ bs = argError "In" [BTerm undefined, BTerm undefined] bs
    mkSymbolApplication "\\not" _ [BPredicate p] = pure $ BPredicate $ Not p
    mkSymbolApplication "\\not" _ bs = argError "Not" [BPredicate undefined] bs
    mkSymbolApplication "\\or" _ [BPredicate p1, BPredicate p2] = pure $ BPredicate $ Or p1 p2
    mkSymbolApplication "\\or" _ bs = argError "Or" [BPredicate undefined, BPredicate undefined] bs
    mkSymbolApplication "\\top" _ [] = pure $ BPredicate Top
    mkSymbolApplication "\\top" _ bs = argError "Top" [] bs
    mkSymbolApplication "inj" [source, target] [BTerm t] = pure $ BTerm $ Injection source target t
    mkSymbolApplication "inj" _ bs = argError "Injection" [BTerm undefined] bs
    mkSymbolApplication name sorts bs =
        lookupKoreDefinitionSymbol name >>= \case
            Just symbol@Symbol{sortVars} -> do
                args <- forM bs $ \case
                    BTerm trm -> pure trm
                    _ -> fail "Expecting term"
                pure $ BTerm $ SymbolApplication symbol (zipWith (const id) sortVars sorts) args
            Nothing -> fail $ "Unknown symbol " <> show name

    argError cons expectedArgs receivedArgs =
        fail $
            "Invalid "
                <> cons
                <> "arguments\nExpected ["
                <> intercalate ", " (map typeOfArg expectedArgs)
                <> "] but got ["
                <> intercalate ", " (map typeOfArg receivedArgs)
                <> "]"

    typeOfArg = \case
        BTerm _ -> "Term"
        BPredicate _ -> "Predicate"
        BString _ -> "String"
        BSort _ -> "Sort"
        BSymbol _ _ -> "Symbol"

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
decodeTerm' :: Maybe KoreDefinition -> Get Term
decodeTerm' mDef = do
    version <- decodeMagicHeaderAndVersion
    runDecodeM version mDef decodeBlock >>= \case
        [BTerm trm] -> pure trm
        _ -> fail "Expecting a single term on the top of the stack"

decodeTerm :: KoreDefinition -> Get Term
decodeTerm = decodeTerm' . Just

decodePattern :: Maybe KoreDefinition -> Get Pattern
decodePattern mDef = do
    version <- decodeMagicHeaderAndVersion
    res <- reverse <$> runDecodeM version mDef decodeBlock
    case res of
        BTerm trm : preds' -> do
            preds <- forM preds' $ \case
                BPredicate p -> pure p
                _ -> fail "Expecting a predicate"
            pure $ Pattern trm preds
        _ -> fail "Expecting a term on the top of the stack"

decodeSingleBlock :: Get Block
decodeSingleBlock = do
    version <- decodeMagicHeaderAndVersion
    runDecodeM version Nothing decodeBlock >>= \case
        [b] -> pure b
        _ -> fail "Expecting a single block on the top of the stack"

test :: Maybe (FilePath, Text.Text) -> FilePath -> IO Term
test (Just (definitionFile, mainModuleName)) f = do
    internalModule <-
        either (error . show) id
            <$> loadDefinition mainModuleName definitionFile
    runGet (decodeTerm internalModule) <$> BL.readFile f
test Nothing f =
    runGet (decodeTerm' Nothing) <$> BL.readFile f

encodeMagicHeaderAndVersion :: Version -> Put
encodeMagicHeaderAndVersion (Version major minor patch) = do
    putByteString "\127KORE"
    putInt16le major
    putInt16le minor
    putInt16le patch

encodeLength :: Int -> Put
encodeLength len =
    let chunk = fromIntegral $ len .&. 0x7f
        len' = len `shiftR` 7
     in if len > 0
            then do
                putWord8 (chunk .|. 0x80)
                encodeLength len'
            else putWord8 chunk

encodeString :: BS.ByteString -> Put
encodeString s = do
    putWord8 0x1
    encodeLength $ BS.length s
    putByteString s

encodeSort :: Sort -> Put
encodeSort = \case
    SortVar name -> do
        putWord8 KORESortVariable
        encodeString name
    SortApp name args -> do
        forM_ args encodeSort
        putWord8 KORECompositeSort
        encodeLength $ length args
        encodeString name

encodeTerm :: Term -> Put
encodeTerm = \case
    Var (Variable sort name) -> do
        encodeSort sort
        putWord8 KOREVariablePattern
        putWord8 KOREVariable
        encodeString name
    SymbolApplication sym sorts args -> encodeSymbolApplication sym.name sorts $ map Left args
    DomainValue sort value -> do
        putWord8 KOREStringPattern
        encodeString value
        encodeSymbol "\\dv" [sort]
        putWord8 KORECompositePattern
        encodeLength 1
    AndTerm t1 t2 -> encodeSymbolApplication "\\and" [sortOfTerm t1] [Left t1, Left t2]
    Injection source target t -> encodeSymbolApplication "inj" [source, target] [Left t]

encodeSymbol :: ByteString -> [Sort] -> Put
encodeSymbol name sorts = do
    forM_ sorts encodeSort
    putWord8 KORESymbol
    encodeLength $ length sorts
    encodeString name

encodeSymbolApplication :: ByteString -> [Sort] -> [Either Term Predicate] -> Put
encodeSymbolApplication name sorts args = do
    forM_ args $ either encodeTerm encodePredicate
    encodeSymbol name sorts
    putWord8 KORECompositePattern
    encodeLength $ length args

encodePredicate :: Predicate -> Put
encodePredicate = \case
    AndPredicate p1 p2 -> encodeSymbolApplication "\\and" [] [Right p1, Right p2]
    Bottom -> encodeSymbolApplication "\\bottom" [] []
    Ceil t -> encodeSymbolApplication "\\ceil" [] [Left t]
    EqualsTerm t1 t2 -> encodeSymbolApplication "\\equals" [] [Left t1, Left t2]
    EqualsPredicate p1 p2 -> encodeSymbolApplication "\\equals" [] [Right p1, Right p2]
    Exists v p ->
        encodeSymbolApplication
            "\\exists"
            []
            [ Left $ Var $ Variable (SortApp "PREDICATE" []) v
            , Right p
            ]
    Forall v p ->
        encodeSymbolApplication
            "\\forall"
            []
            [ Left $ Var $ Variable (SortApp "PREDICATE" []) v
            , Right p
            ]
    Iff p1 p2 -> encodeSymbolApplication "\\iff" [] [Right p1, Right p2]
    Implies p1 p2 -> encodeSymbolApplication "\\implies" [] [Right p1, Right p2]
    In t1 t2 -> encodeSymbolApplication "\\in" [] [Left t1, Left t2]
    Not p -> encodeSymbolApplication "\\not" [] [Right p]
    Or p1 p2 -> encodeSymbolApplication "\\or" [] [Right p1, Right p2]
    Top -> encodeSymbolApplication "\\top" [] []

encodePattern :: Pattern -> Put
encodePattern Pattern{term, constraints} = do
    encodeTerm term
    forM_ constraints encodePredicate

encodeSingleBlock :: Block -> Put
encodeSingleBlock = \case
    BTerm t -> encodeTerm t
    BPredicate p -> encodePredicate p
    BString s -> encodeString s
    BSort s -> encodeSort s
    BSymbol name sorts -> encodeSymbol name sorts

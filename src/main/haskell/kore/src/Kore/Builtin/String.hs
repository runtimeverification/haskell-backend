{- |
Module      : Kore.Builtin.String
Description : Built-in string sort
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.String as String
@
 -}

module Kore.Builtin.String
    ( sort
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , patternVerifier
    , builtinFunctions
    , expectBuiltinString
    , asMetaPattern
    , asPattern
    , asConcretePattern
    , asExpandedPattern
    , asPartialExpandedPattern
    , parse
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Control.Monad
                 ( void )
import           Data.Char
                 ( chr, ord )
import qualified Data.HashMap.Strict as HashMap
import           Data.List
                 ( findIndex )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Read as Text
import           Numeric
                 ( readOct )
import qualified Text.Megaparsec as Parsec

import           Kore.Annotation.Valid
import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

{- | Builtin name of the @String@ sort.
 -}
sort :: Text
sort = "STRING.String"


{- | Verify that the sort is hooked to the builtin @String@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort findSort = Builtin.verifySort findSort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [   ( ltKeyT
        , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
        )
    ,   ( plusKeyT
        , Builtin.verifySymbol assertSort [assertSort, assertSort]
        )
    ,   ( substrKeyT
        , Builtin.verifySymbol
            assertSort
            [assertSort, Int.assertSort, Int.assertSort]
        )
    ,   ( lengthKeyT
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ,   ( findKeyT
        , Builtin.verifySymbol
            Int.assertSort
            [assertSort, assertSort, Int.assertSort]
        )
    ,   ( string2BaseKeyT
        , Builtin.verifySymbol
            Int.assertSort
            [assertSort, Int.assertSort]
        )
    ,   ( string2IntKeyT
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ,   ( chrKeyT
        , Builtin.verifySymbol assertSort [Int.assertSort]
        )
    ,   ( ordKeyT
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.PatternVerifier
patternVerifier =
    Builtin.verifyDomainValue sort
    (void . Builtin.parseDomainValue parse)

{- | Parse a string literal.
 -}
parse :: Builtin.Parser Text
parse = Text.pack <$> Parsec.many Parsec.anySingle

{- | Abort function evaluation if the argument is not a String domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinString
    :: Monad m
    => Text  -- ^ Context for error message
    -> StepPattern Object variable  -- ^ Operand pattern
    -> MaybeT m Text
expectBuiltinString ctx =
    \case
        DV_ _ domain ->
            case domain of
                Domain.BuiltinPattern (StringLiteral_ lit) ->
                    (return . Builtin.runParser ctx)
                        (Builtin.parseString parse lit)
                _ ->
                    Builtin.verifierBug
                        (Text.unpack ctx ++ ": Domain value argument is not a string")
        _ ->
            empty

{- | Render an 'String' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> StepPattern Object variable
asPattern resultSort result =
    fromConcreteStepPattern (asConcretePattern resultSort result)

{- | Render a 'String' as a concrete domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asConcretePattern
    :: Sort Object  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> ConcreteStepPattern Object
asConcretePattern domainValueSort =
    mkDomainValue domainValueSort
        . Domain.BuiltinPattern
        . eraseAnnotations
        . asMetaPattern

asMetaPattern
    :: Functor domain
    => Text
    -> PurePattern Meta domain variable (Valid (variable Meta) Meta)
asMetaPattern = mkStringLiteral

asExpandedPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asPattern resultSort

asPartialExpandedPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Maybe Text  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asPartialExpandedPattern resultSort =
    maybe ExpandedPattern.bottom (asExpandedPattern resultSort)

ltKeyT :: Text
ltKeyT = "STRING.lt"

plusKeyT :: Text
plusKeyT = "STRING.concat"

string2IntKey :: String
string2IntKey = "STRING.string2int"
string2IntKeyT :: Text
string2IntKeyT = "STRING.string2int"

substrKey :: String
substrKey = "STRING.substr"
substrKeyT :: Text
substrKeyT = "STRING.substr"

lengthKey :: String
lengthKey = "STRING.length"
lengthKeyT :: Text
lengthKeyT = "STRING.length"

findKey :: String
findKey = "STRING.find"
findKeyT :: Text
findKeyT = "STRING.find"

string2BaseKey :: String
string2BaseKey = "STRING.string2base"
string2BaseKeyT :: Text
string2BaseKeyT = "STRING.string2base"

chrKey :: String
chrKey = "STRING.chr"
chrKeyT :: Text
chrKeyT = "STRING.chr"

ordKey :: String
ordKey = "STRING.ord"
ordKeyT :: Text
ordKeyT = "STRING.ord"

evalSubstr :: Builtin.Function
evalSubstr = Builtin.functionEvaluator evalSubstr0
  where
    substr :: Int -> Int -> Text -> Text
    substr startIndex endIndex =
        Text.take (endIndex - startIndex) . Text.drop startIndex
    evalSubstr0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalSubstr0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let (_str, _start, _end) =
                    case arguments of
                        [_str, _start, _end] -> (_str, _start, _end)
                        _                    -> Builtin.wrongArity substrKey
            _str   <- expectBuiltinString substrKeyT _str
            _start <- fromInteger <$> Int.expectBuiltinInt substrKeyT _start
            _end   <- fromInteger <$> Int.expectBuiltinInt substrKeyT _end
            Builtin.appliedFunction
                . asExpandedPattern resultSort
                $ substr _start _end _str

evalLength :: Builtin.Function
evalLength = Builtin.functionEvaluator evalLength0
  where
    evalLength0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalLength0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _      -> Builtin.wrongArity lengthKey
            _str <- expectBuiltinString lengthKeyT _str
            Builtin.appliedFunction
                . Int.asExpandedPattern resultSort
                . toInteger
                $ Text.length _str

evalFind :: Builtin.Function
evalFind = Builtin.functionEvaluator evalFind0
  where
    maybeNotFound :: Maybe Int -> Integer
    maybeNotFound = maybe (-1) toInteger

    evalFind0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalFind0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let (_str, _substr, _idx) =
                    case arguments of
                        [_str, _substr, _idx] -> (_str, _substr, _idx)
                        _                     -> Builtin.wrongArity findKey
            _str <- expectBuiltinString findKeyT _str
            _substr <- expectBuiltinString findKeyT _substr
            _idx <- fromInteger <$> Int.expectBuiltinInt substrKeyT _idx
            Builtin.appliedFunction
                . Int.asExpandedPattern resultSort
                . maybeNotFound
                $ findIndex (Text.isPrefixOf _substr) (Text.tails . Text.drop _idx $ _str)

evalString2Base :: Builtin.Function
evalString2Base = Builtin.functionEvaluator evalString2Base0
  where
    evalString2Base0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalString2Base0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let (_str, _base) =
                    case arguments of
                        [_str, _base] -> (_str, _base)
                        _             -> Builtin.wrongArity string2BaseKey
            _str  <- expectBuiltinString string2BaseKeyT _str
            _base <- Int.expectBuiltinInt string2BaseKeyT _base
            let readN =
                    case _base of
                        -- no builtin reader for number in octal notation
                        8  -> \s ->
                            case readOct $ Text.unpack s of
                                [(result, "")] -> Right (result, "")
                                _              -> Left ""
                        10 -> Text.signed Text.decimal
                        16 -> Text.hexadecimal
                        _  -> const empty
            case readN _str of
                Right (result, Text.unpack -> "") ->
                    Builtin.appliedFunction
                        . Int.asExpandedPattern resultSort
                        $ result
                _ ->
                    Builtin.appliedFunction ExpandedPattern.bottom

evalString2Int :: Builtin.Function
evalString2Int = Builtin.functionEvaluator evalString2Int0
  where
    evalString2Int0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalString2Int0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _      -> Builtin.wrongArity string2IntKey
            _str <- expectBuiltinString string2IntKeyT _str
            case Text.signed Text.decimal _str of
                Right (result, Text.unpack -> "") ->
                    Builtin.appliedFunction
                    . Int.asExpandedPattern resultSort
                    $ result
                _ ->
                    Builtin.appliedFunction ExpandedPattern.bottom

evalChr :: Builtin.Function
evalChr = Builtin.functionEvaluator evalChr0
    where
    evalChr0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalChr0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let _n =
                    case arguments of
                        [_n] -> _n
                        _    -> Builtin.wrongArity chrKey
            _n <- Int.expectBuiltinInt chrKeyT _n
            Builtin.appliedFunction
                . asExpandedPattern resultSort
                $ Text.singleton $ chr $ fromIntegral _n

evalOrd :: Builtin.Function
evalOrd = Builtin.functionEvaluator evalOrd0
    where
    evalOrd0
        :: (Ord (variable Object), Show (variable Object))
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalOrd0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _    -> Builtin.wrongArity ordKey
            _str <- expectBuiltinString ordKeyT _str
            Builtin.appliedFunction
                . maybe ExpandedPattern.bottom charToOrdInt
                $ if Text.length _str == 1
                      then Just (Text.head _str)
                      else Nothing
      where
        charToOrdInt =
            Int.asExpandedPattern resultSort
            . toInteger
            . ord

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
    [ comparator ltKeyT (<)
    , binaryOperator plusKeyT Text.append
    , (substrKeyT, evalSubstr)
    , (lengthKeyT, evalLength)
    , (findKeyT, evalFind)
    , (string2BaseKeyT, evalString2Base)
    , (string2IntKeyT, evalString2Int)
    , (chrKeyT, evalChr)
    , (ordKeyT, evalOrd)
    ]
  where
    comparator name op =
        (name, Builtin.binaryOperator parse Bool.asExpandedPattern name op)
    binaryOperator name op =
        (name, Builtin.binaryOperator parse asExpandedPattern name op)

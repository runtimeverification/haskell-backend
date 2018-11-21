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
import qualified Data.Functor.Foldable as Functor.Foldable
import qualified Data.HashMap.Strict as HashMap
import           Data.List
                 ( findIndex, isPrefixOf, tails )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
                 ( listToMaybe )
import           Data.Text
                 ( Text )
import           Numeric
                 ( readDec, readHex, readOct, readSigned )
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Parsec

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Meta, Object )
import           Kore.AST.PureML
                 ( fromConcretePurePattern )
import           Kore.ASTUtils.SmartPatterns
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
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.PatternVerifier
patternVerifier =
    Builtin.verifyDomainValue sort
    (void . Builtin.parseDomainValue parse)

{- | Parse a string literal.
 -}
parse :: Builtin.Parser String
parse = Parsec.many Parsec.anyChar

{- | Abort function evaluation if the argument is not a String domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinString
    :: Monad m
    => String  -- ^ Context for error message
    -> StepPattern Object variable  -- ^ Operand pattern
    -> MaybeT m String
expectBuiltinString ctx =
    \case
        DV_ _ domain ->
            case domain of
                Domain.BuiltinPattern (StringLiteral_ lit) ->
                    (return . Builtin.runParser ctx)
                        (Builtin.parseString parse lit)
                _ ->
                    Builtin.verifierBug
                        (ctx ++ ": Domain value argument is not a string")
        _ ->
            empty

{- | Render an 'String' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Sort Object  -- ^ resulting sort
    -> String  -- ^ builtin value to render
    -> StepPattern Object variable
asPattern resultSort result =
    fromConcretePurePattern (asConcretePattern resultSort result)

{- | Render a 'String' as a concrete domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asConcretePattern
    :: Sort Object  -- ^ resulting sort
    -> String  -- ^ builtin value to render
    -> ConcreteStepPattern Object
asConcretePattern domainValueSort result =
    (Functor.Foldable.embed . DomainValuePattern)
        DomainValue
            { domainValueSort
            , domainValueChild = Domain.BuiltinPattern $ asMetaPattern result
            }

asMetaPattern :: String -> CommonPurePattern Meta dom
asMetaPattern result = StringLiteral_ $ result

asExpandedPattern
    :: Sort Object  -- ^ resulting sort
    -> String  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asPattern resultSort

asPartialExpandedPattern
    :: Sort Object  -- ^ resulting sort
    -> Maybe String  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asPartialExpandedPattern resultSort =
    maybe ExpandedPattern.bottom (asExpandedPattern resultSort)

ltKeyT :: Text
ltKeyT = "STRING.lt"

plusKeyT :: Text
plusKeyT = "STRING.concat"

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

evalSubstr :: Builtin.Function
evalSubstr = Builtin.functionEvaluator evalSubstr0
  where
    substr :: Int -> Int -> String -> String
    substr startIndex endIndex =
        take (endIndex - startIndex) . drop startIndex
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
            _str   <- expectBuiltinString substrKey _str
            _start <- fromInteger <$> Int.expectBuiltinInt substrKey _start
            _end   <- fromInteger <$> Int.expectBuiltinInt substrKey _end
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
            _str <- expectBuiltinString lengthKey _str
            Builtin.appliedFunction
                . Int.asExpandedPattern resultSort
                . toInteger
                $ length _str

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
            _str <- expectBuiltinString findKey _str
            _substr <- expectBuiltinString findKey _substr
            _idx <- fromInteger <$> Int.expectBuiltinInt substrKey _idx
            Builtin.appliedFunction
                . Int.asExpandedPattern resultSort
                . maybeNotFound
                $ findIndex (isPrefixOf _substr) (tails . drop _idx $ _str)

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
                        _             -> Builtin.wrongArity findKey
            _str  <- expectBuiltinString string2BaseKey _str
            _base <- Int.expectBuiltinInt string2BaseKey _base
            readN <- case _base of
                8  -> pure readOct
                10 -> pure . readSigned $ readDec
                16 -> pure readHex
                _  -> pure $ const empty
            case readN _str of
                [(result, "")] ->
                    Builtin.appliedFunction
                        . Int.asExpandedPattern resultSort
                        $ result
                _                 ->
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
                        _      -> Builtin.wrongArity findKey
            _str <- expectBuiltinString findKey _str
            Builtin.appliedFunction
                . maybe
                    ExpandedPattern.bottom
                    (Int.asExpandedPattern resultSort)
                . fmap fst . listToMaybe . readSigned readDec
                $ _str

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
    [ comparator ltKeyT (<)
    , binaryOperator plusKeyT (++)
    , (substrKeyT, evalSubstr)
    , (lengthKeyT, evalLength)
    , (findKeyT, evalFind)
    , (string2BaseKeyT, evalString2Base)
    , (string2IntKeyT, evalString2Int)
    ]
  where
    comparator name op =
        (name, Builtin.binaryOperator parse Bool.asExpandedPattern name op)
    binaryOperator name op =
        (name, Builtin.binaryOperator parse asExpandedPattern name op)

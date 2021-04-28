{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Builtin.Bool (
    sort,
    assertSort,
    verifiers,
    builtinFunctions,
    asInternal,
    asTermLike,
    asPattern,
    extractBoolDomainValue,
    parse,
    unifyBool,
    unifyBoolAnd,
    unifyBoolOr,
    unifyBoolNot,
    matchBool,

    -- * Keys
    orKey,
    andKey,
    xorKey,
    neKey,
    eqKey,
    notKey,
    impliesKey,
    andThenKey,
    orElseKey,
) where

import Control.Error (
    MaybeT,
 )
import qualified Control.Monad as Monad
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Builtin.Bool.Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error
import Kore.Internal.InternalBool
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify (
    BuiltinAndAxiomSimplifier,
    TermSimplifier,
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import qualified Kore.Unification.Unify as Unify
import Prelude.Kore
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Parsec

{- | Verify that the sort is hooked to the builtin @Bool@ sort.

  See also: 'sort', 'Builtin.verifySort'
-}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook
        }

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'
-}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [(sort, Builtin.verifySortDecl)]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'
-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [ (orKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (andKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (xorKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (neKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (eqKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (notKey, Builtin.verifySymbol assertSort [assertSort])
        , (impliesKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (andThenKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (orElseKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        ]

-- | Verify that domain value patterns are well-formed.
patternVerifierHook :: Builtin.PatternVerifierHook
patternVerifierHook =
    Builtin.domainValuePatternVerifierHook sort patternVerifierWorker
  where
    patternVerifierWorker domainValue =
        case externalChild of
            StringLiteral_ lit -> do
                internalBoolValue <- Builtin.parseString parse lit
                (return . InternalBoolF . Const)
                    InternalBool
                        { internalBoolSort = domainValueSort
                        , internalBoolValue
                        }
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue{domainValueSort} = domainValue
        DomainValue{domainValueChild = externalChild} = domainValue

-- | get the value from a (possibly encoded) domain value
extractBoolDomainValue ::
    -- | error message Context
    Text ->
    TermLike variable ->
    Maybe Bool
extractBoolDomainValue _ = matchBool

-- | Parse an integer string literal.
parse :: Builtin.Parser Bool
parse = (Parsec.<|>) true false
  where
    true = Parsec.string "true" $> True
    false = Parsec.string "false" $> False

-- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
builtinFunctions :: Map Text BuiltinAndAxiomSimplifier
builtinFunctions =
    Map.fromList
        [ (orKey, binaryOperator orKey (||))
        , (andKey, binaryOperator andKey (&&))
        , (xorKey, binaryOperator xorKey xor)
        , (neKey, binaryOperator neKey (/=))
        , (eqKey, binaryOperator eqKey (==))
        , (notKey, unaryOperator notKey not)
        , (impliesKey, binaryOperator impliesKey implies)
        , (andThenKey, binaryOperator andThenKey (&&))
        , (orElseKey, binaryOperator orElseKey (||))
        ]
  where
    unaryOperator =
        Builtin.unaryOperator extractBoolDomainValue asPattern
    binaryOperator =
        Builtin.binaryOperator extractBoolDomainValue asPattern
    xor a b = (a && not b) || (not a && b)
    implies a b = not a || b

-- | Unification of @BOOL.Bool@ values.
unifyBool ::
    forall variable unifier.
    InternalVariable variable =>
    MonadUnify unifier =>
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyBool a b =
    worker a b <|> worker b a
  where
    worker termLike1 termLike2
        | Just value1 <- matchBool termLike1
          , Just value2 <- matchBool termLike2 =
            lift $
                if value1 == value2
                    then return (Pattern.fromTermLike termLike1)
                    else
                        Unify.explainAndReturnBottom
                            "different Bool domain values"
                            termLike1
                            termLike2
    worker _ _ = empty

unifyBoolAnd ::
    forall variable unifier.
    InternalVariable variable =>
    MonadUnify unifier =>
    TermSimplifier variable unifier ->
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyBoolAnd unifyChildren a b =
    worker a b <|> worker b a
  where
    worker termLike1 termLike2
        | Just value1 <- matchBool termLike1
          , value1
          , Just BoolAnd{operand1, operand2} <- matchBoolAnd termLike2
          , isFunctionPattern termLike2 =
            unifyBothWith unifyChildren termLike1 operand1 operand2
    worker _ _ = empty

{- |Takes a (function-like) pattern and unifies it against two other patterns.
   Returns the original pattern and the conditions resulting from unification.
-}
unifyBothWith ::
    forall variable unifier.
    InternalVariable variable =>
    MonadUnify unifier =>
    -- | unification (simplification) function
    TermSimplifier variable unifier ->
    -- | base term to unify next terms against (assumed function-like)
    TermLike variable ->
    -- | first term to be unified with the base term
    TermLike variable ->
    -- | first term to be unified with the base term
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyBothWith unify termLike1 operand1 operand2 = lift $ do
    unification1 <- unify' termLike1 operand1
    unification2 <- unify' termLike1 operand2
    let conditions = unification1 <> unification2
    pure (Pattern.withCondition termLike1 conditions)
  where
    unify' term1 term2 =
        Pattern.withoutTerm <$> unify term1 term2

unifyBoolOr ::
    forall variable unifier.
    InternalVariable variable =>
    MonadUnify unifier =>
    TermSimplifier variable unifier ->
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyBoolOr unifyChildren a b =
    worker a b <|> worker b a
  where
    worker termLike1 termLike2
        | Just value1 <- matchBool termLike1
          , not value1
          , Just BoolOr{operand1, operand2} <- matchBoolOr termLike2
          , isFunctionPattern termLike2 =
            unifyBothWith unifyChildren termLike1 operand1 operand2
    worker _ _ = empty

unifyBoolNot ::
    forall variable unifier.
    InternalVariable variable =>
    MonadUnify unifier =>
    TermSimplifier variable unifier ->
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)
unifyBoolNot unifyChildren a b =
    worker a b <|> worker b a
  where
    worker termLike1 boolTerm
        | Just BoolNot{operand} <- matchBoolNot termLike1
          , isFunctionPattern termLike1
          , Just value <- matchBool boolTerm =
            lift $ do
                let notValue = asInternal (termLikeSort boolTerm) (not value)
                unifyChildren notValue operand
    worker _ _ = empty

-- | Match a @BOOL.Bool@ builtin value.
matchBool :: TermLike variable -> Maybe Bool
matchBool (InternalBool_ InternalBool{internalBoolValue}) =
    Just internalBoolValue
matchBool _ = Nothing

-- | The @BOOL.and@ hooked symbol applied to @term@-type arguments.
data BoolAnd term = BoolAnd
    { symbol :: !Symbol
    , operand1, operand2 :: !term
    }

-- | Match the @BOOL.and@ hooked symbol.
matchBoolAnd :: TermLike variable -> Maybe (BoolAnd (TermLike variable))
matchBoolAnd (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == andKey)
    return BoolAnd{symbol, operand1, operand2}
matchBoolAnd _ = Nothing

-- | The @BOOL.or@ hooked symbol applied to @term@-type arguments.
data BoolOr term = BoolOr
    { symbol :: !Symbol
    , operand1, operand2 :: !term
    }

-- | Match the @BOOL.or@ hooked symbol.
matchBoolOr :: TermLike variable -> Maybe (BoolOr (TermLike variable))
matchBoolOr (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == orKey)
    return BoolOr{symbol, operand1, operand2}
matchBoolOr _ = Nothing

-- | The @BOOL.not@ hooked symbol applied to a @term@-type argument.
data BoolNot term = BoolNot
    { symbol :: !Symbol
    , operand :: !term
    }

-- | Match the @BOOL.not@ hooked symbol.
matchBoolNot :: TermLike variable -> Maybe (BoolNot (TermLike variable))
matchBoolNot (App_ symbol [operand]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == notKey)
    return BoolNot{symbol, operand}
matchBoolNot _ = Nothing

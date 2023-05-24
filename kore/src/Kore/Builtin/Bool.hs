{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.Bool (
    sort,
    assertSort,
    verifiers,
    builtinFunctions,
    asInternal,
    asPattern,
    extractBoolDomainValue,
    parse,
    unifyBool,
    unifyBoolAnd,
    unifyBoolOr,
    unifyBoolNot,
    matchBool,
    matchBools,
    matchUnifyBoolAnd,
    matchUnifyBoolOr,
    matchUnifyBoolNot,

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

import Control.Monad qualified as Monad
import Data.Functor.Const
import Data.HashMap.Strict qualified as HashMap
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Builtin.Bool.Bool
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Error qualified
import Kore.Internal.InternalBool
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
    TermSimplifier,
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import Prelude.Kore
import Text.Megaparsec qualified as Parsec
import Text.Megaparsec.Char qualified as Parsec

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
builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == orKey = Just $ binaryOperator orKey (||)
    | key == andKey = Just $ binaryOperator andKey (&&)
    | key == xorKey = Just $ binaryOperator xorKey xor
    | key == neKey = Just $ binaryOperator neKey (/=)
    | key == eqKey = Just $ binaryOperator eqKey (==)
    | key == notKey = Just $ unaryOperator notKey not
    | key == impliesKey = Just $ binaryOperator impliesKey implies
    | key == andThenKey = Just $ binaryOperator andThenKey (&&)
    | key == orElseKey = Just $ binaryOperator orElseKey (||)
    | otherwise = Nothing
  where
    unaryOperator =
        Builtin.unaryOperator extractBoolDomainValue asPattern
    binaryOperator =
        Builtin.binaryOperator extractBoolDomainValue asPattern
    xor a b = (a && not b) || (not a && b)
    implies a b = not a || b

data UnifyBool = UnifyBool
    { bool1, bool2 :: !InternalBool
    , term1, term2 :: !(TermLike RewritingVariableName)
    }

{- | Matches

@
\\equals{_, _}(\\dv{Bool}(_), \\dv{Bool}(_))
@

and

@
\\and{_}(\\dv{Bool}(_), \\dv{Bool}(_))
@
-}
matchBools ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyBool
matchBools term1 term2
    | InternalBool_ bool1 <- term2
    , InternalBool_ bool2 <- term1 =
        Just UnifyBool{bool1, bool2, term1, term2}
    | otherwise = Nothing
{-# INLINE matchBools #-}

-- | When bool values are equal, returns first term; otherwise returns bottom.
unifyBool ::
    forall unifier.
    MonadUnify unifier =>
    UnifyBool ->
    unifier (Pattern RewritingVariableName)
unifyBool unifyData
    | bool1 == bool2 =
        return (Pattern.fromTermLike term1)
    | otherwise =
        debugUnifyBottomAndReturnBottom
            "different Bool domain values"
            term1
            term2
  where
    UnifyBool{bool1, bool2, term1, term2} = unifyData

data UnifyBoolAnd = UnifyBoolAnd
    { term :: !(TermLike RewritingVariableName)
    , boolAnd :: !BoolAnd
    }

{- | Matches

@
\\equals{_, _}(\\dv{Bool}("true"), andBool(_,_))
@

and

@
\\and{_}(\\dv{Bool}("true"), andBool(_,_)),
@

symmetric in the two arguments.
-}
matchUnifyBoolAnd ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyBoolAnd
matchUnifyBoolAnd first second
    | Just True <- matchBool first
    , Just boolAnd <- matchBoolAnd second
    , isFunctionPattern second =
        Just $ UnifyBoolAnd{term = first, boolAnd}
    | Just True <- matchBool second
    , Just boolAnd <- matchBoolAnd first
    , isFunctionPattern first =
        Just $ UnifyBoolAnd{term = second, boolAnd}
    | otherwise =
        Nothing
{-# INLINE matchUnifyBoolAnd #-}

unifyBoolAnd ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    UnifyBoolAnd ->
    unifier (Pattern RewritingVariableName)
unifyBoolAnd unifyChildren unifyData =
    unifyBothWith unifyChildren term operand1 operand2
  where
    UnifyBoolAnd{term, boolAnd} = unifyData
    BoolAnd{operand1, operand2} = boolAnd

{- | Takes a (function-like) pattern and unifies it against two other patterns.
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
    unifier (Pattern variable)
unifyBothWith unify termLike1 operand1 operand2 = do
    unification1 <- unify' termLike1 operand1
    unification2 <- unify' termLike1 operand2
    let conditions = unification1 <> unification2
    pure (Pattern.withCondition termLike1 conditions)
  where
    unify' term1 term2 =
        Pattern.withoutTerm <$> unify term1 term2

data UnifyBoolOr = UnifyBoolOr
    { term :: !(TermLike RewritingVariableName)
    , boolOr :: !BoolOr
    }

{- | Matches

@
\\equals{_, _}(\\dv{Bool}("false"), boolOr(_,_))
@

and

@
\\and{_}(\\dv{Bool}("false"), boolOr(_,_)),
@

symmetric in the two arguments.
-}
matchUnifyBoolOr ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyBoolOr
matchUnifyBoolOr first second
    | Just False <- matchBool first
    , Just boolOr <- matchBoolOr second
    , isFunctionPattern second =
        Just UnifyBoolOr{term = first, boolOr}
    | Just False <- matchBool second
    , Just boolOr <- matchBoolOr first
    , isFunctionPattern first =
        Just UnifyBoolOr{term = second, boolOr}
    | otherwise = Nothing
{-# INLINE matchUnifyBoolOr #-}

unifyBoolOr ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    UnifyBoolOr ->
    unifier (Pattern RewritingVariableName)
unifyBoolOr unifyChildren unifyData =
    unifyBothWith unifyChildren term operand1 operand2
  where
    UnifyBoolOr{term, boolOr} = unifyData
    BoolOr{operand1, operand2} = boolOr

data UnifyBoolNot = UnifyBoolNot
    { boolNot :: !BoolNot
    , value :: !InternalBool
    }

{- | Matches

@
\\equals{_, _}(notBool(_), \\dv{Bool}(_))
@

and

@
\\and{_}(notBool(_), \\dv{Bool}(_)),
@

symmetric in the two arguments.
-}
matchUnifyBoolNot ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyBoolNot
matchUnifyBoolNot first second
    | Just boolNot <- matchBoolNot first
    , isFunctionPattern first
    , Just value <- matchInternalBool second =
        Just UnifyBoolNot{boolNot, value}
    | Just boolNot <- matchBoolNot second
    , isFunctionPattern second
    , Just value <- matchInternalBool first =
        Just UnifyBoolNot{boolNot, value}
    | otherwise = Nothing
{-# INLINE matchUnifyBoolNot #-}

unifyBoolNot ::
    forall unifier.
    TermSimplifier RewritingVariableName unifier ->
    UnifyBoolNot ->
    unifier (Pattern RewritingVariableName)
unifyBoolNot unifyChildren unifyData =
    let notValue = asInternal internalBoolSort (not internalBoolValue)
     in unifyChildren notValue operand
  where
    UnifyBoolNot{boolNot, value} = unifyData
    InternalBool{internalBoolValue, internalBoolSort} = value
    BoolNot{operand} = boolNot

matchInternalBool :: TermLike variable -> Maybe InternalBool
matchInternalBool (InternalBool_ internalBool) =
    Just internalBool
matchInternalBool _ = Nothing

-- | Match a @BOOL.Bool@ builtin value.
matchBool :: TermLike variable -> Maybe Bool
matchBool (InternalBool_ InternalBool{internalBoolValue}) =
    Just internalBoolValue
matchBool _ = Nothing

-- | The @BOOL.and@ hooked symbol applied to @term@-type arguments.
data BoolAnd = BoolAnd
    { symbol :: !Symbol
    , operand1, operand2 :: !(TermLike RewritingVariableName)
    }

-- | Match the @BOOL.and@ hooked symbol.
matchBoolAnd :: TermLike RewritingVariableName -> Maybe BoolAnd
matchBoolAnd (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == andKey)
    return BoolAnd{symbol, operand1, operand2}
matchBoolAnd _ = Nothing

-- | The @BOOL.or@ hooked symbol applied to @term@-type arguments.
data BoolOr = BoolOr
    { symbol :: !Symbol
    , operand1, operand2 :: !(TermLike RewritingVariableName)
    }

-- | Match the @BOOL.or@ hooked symbol.
matchBoolOr :: TermLike RewritingVariableName -> Maybe BoolOr
matchBoolOr (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == orKey)
    return BoolOr{symbol, operand1, operand2}
matchBoolOr _ = Nothing

-- | The @BOOL.not@ hooked symbol applied to a @term@-type argument.
data BoolNot = BoolNot
    { symbol :: !Symbol
    , operand :: !(TermLike RewritingVariableName)
    }

-- | Match the @BOOL.not@ hooked symbol.
matchBoolNot :: TermLike RewritingVariableName -> Maybe BoolNot
matchBoolNot (App_ symbol [operand]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == notKey)
    return BoolNot{symbol, operand}
matchBoolNot _ = Nothing

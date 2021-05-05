{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

{-# LANGUAGE Strict #-}

module Kore.Builtin.Bool
    ( sort
    , assertSort
    , verifiers
    , builtinFunctions
    , asInternal
    , asTermLike
    , asPattern
    , extractBoolDomainValue
    , parse
    , unifyBool
    , unifyBoolAnd
    , unifyBoolOr
    , unifyBoolNot
    , matchBool
    , matchBools
    , matchBoolAnd
    , matchBoolNot
    , matchBoolOr
    , matchUnifyBoolAnd
    , matchUnifyBoolOr
    , matchUnifyBoolNot
    , BoolAnd (..)
    , BoolNot (..)
    , BoolOr (..)
      -- * Keys
    , orKey
    , andKey
    , xorKey
    , neKey
    , eqKey
    , notKey
    , impliesKey
    , andThenKey
    , orElseKey
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    )
import qualified Control.Monad as Monad
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Parsec

import Kore.Attribute.Hook
    ( Hook (..)
    )
import Kore.Builtin.Bool.Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error
import Kore.Internal.InternalBool
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifier
    , TermSimplifier
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Unify

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
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

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

{- | Verify that domain value patterns are well-formed.
 -}
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
        DomainValue { domainValueSort } = domainValue
        DomainValue { domainValueChild = externalChild } = domainValue

-- | get the value from a (possibly encoded) domain value
extractBoolDomainValue
    :: Text -- ^ error message Context
    -> TermLike variable
    -> Maybe Bool
extractBoolDomainValue _ = matchBool

{- | Parse an integer string literal.
 -}
parse :: Builtin.Parser Bool
parse = (Parsec.<|>) true false
  where
    true = Parsec.string "true" $> True
    false = Parsec.string "false" $> False

{- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
 -}
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

data UnifyBool = UnifyBool {
    bool1, bool2 :: InternalBool
}

matchBools
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyBool
matchBools first second
    | InternalBool_ bool1 <- first
    , InternalBool_ bool2 <- second
        = Just $ UnifyBool bool1 bool2
    | otherwise = Nothing
{-# INLINE matchBools #-}

{- | Unification of @BOOL.Bool@ values.
 -}
unifyBool
    :: forall unifier
     . MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> UnifyBool
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyBool first second unifyData =
    worker bool1 bool2 <|> worker bool2 bool1
  where
    worker value1 value2
      = lift $ if value1 == value2
            then return (Pattern.fromTermLike first)
            else
                Unify.explainAndReturnBottom
                    "different Bool domain values"
                    first
                    second

    UnifyBool { bool1, bool2 } = unifyData

matchUnifyBoolAnd
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe (BoolAnd (TermLike RewritingVariableName))
matchUnifyBoolAnd first second
    | Just value1 <- matchBool first
    , value1
    , Just boolAnd <- matchBoolAnd second
    , isFunctionPattern second
        = Just boolAnd
    | otherwise = Nothing
{-# INLINE matchUnifyBoolAnd #-}

unifyBoolAnd
    :: forall unifier
    .  MonadUnify unifier
    => TermSimplifier RewritingVariableName unifier
    -> TermLike RewritingVariableName
    -> BoolAnd (TermLike RewritingVariableName)
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyBoolAnd unifyChildren termLike1 boolAnd =
    unifyBothWith unifyChildren termLike1 operand1 operand2
  where
    BoolAnd { operand1, operand2 } = boolAnd

{-|Takes a (function-like) pattern and unifies it against two other patterns.
   Returns the original pattern and the conditions resulting from unification.
-}
unifyBothWith
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermSimplifier variable unifier
    -- ^ unification (simplification) function
    -> TermLike variable
    -- ^ base term to unify next terms against (assumed function-like)
    -> TermLike variable
    -- ^ first term to be unified with the base term
    -> TermLike variable
    -- ^ first term to be unified with the base term
    -> MaybeT unifier (Pattern variable)
unifyBothWith unify termLike1 operand1 operand2 = lift $ do
    unification1 <- unify' termLike1 operand1
    unification2 <- unify' termLike1 operand2
    let conditions = unification1 <> unification2
    pure (Pattern.withCondition termLike1 conditions)
  where
    unify' term1 term2 =
        Pattern.withoutTerm <$> unify term1 term2

matchUnifyBoolOr
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe (BoolOr (TermLike RewritingVariableName))
matchUnifyBoolOr first second
    | Just value1 <- matchBool first
    , not value1
    , Just boolOr <- matchBoolOr second
    , isFunctionPattern second
    = Just boolOr
    | otherwise = Nothing
{-# INLINE matchUnifyBoolOr #-}

unifyBoolOr
    :: forall unifier
    .  MonadUnify unifier
    => TermSimplifier RewritingVariableName unifier
    -> TermLike RewritingVariableName
    -> BoolOr (TermLike RewritingVariableName)
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyBoolOr unifyChildren termLike boolOr
      = unifyBothWith unifyChildren termLike operand1 operand2
  where
    BoolOr { operand1, operand2 } = boolOr

data UnifyBoolNot = UnifyBoolNot {
    boolNot :: BoolNot (TermLike RewritingVariableName)
    , value :: Bool
}

matchUnifyBoolNot
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyBoolNot
matchUnifyBoolNot first second
    | Just boolNot <- matchBoolNot first
    , isFunctionPattern first
    , Just value <- matchBool second
    = Just $ UnifyBoolNot boolNot value
    | otherwise = Nothing
{-# INLINE matchUnifyBoolNot #-}

unifyBoolNot
    :: forall unifier
    .  MonadUnify unifier
    => TermSimplifier RewritingVariableName unifier
    -> TermLike RewritingVariableName
    -> UnifyBoolNot
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyBoolNot unifyChildren term unifyData =
    let notValue = asInternal (termLikeSort term) (not value) in
        lift $ unifyChildren notValue operand

  where
    UnifyBoolNot { boolNot, value } = unifyData
    BoolNot { operand } = boolNot

{- | Match a @BOOL.Bool@ builtin value.
 -}
matchBool :: TermLike variable -> Maybe Bool
matchBool (InternalBool_ InternalBool { internalBoolValue }) =
    Just internalBoolValue
matchBool _ = Nothing

{- | The @BOOL.and@ hooked symbol applied to @term@-type arguments.
 -}
data BoolAnd term =
    BoolAnd
        { symbol :: !Symbol
        , operand1, operand2 :: !term
        }

{- | Match the @BOOL.and@ hooked symbol.
 -}
matchBoolAnd :: TermLike variable -> Maybe (BoolAnd (TermLike variable))
matchBoolAnd (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == andKey)
    return BoolAnd { symbol, operand1, operand2 }
matchBoolAnd _ = Nothing

{- | The @BOOL.or@ hooked symbol applied to @term@-type arguments.
 -}
data BoolOr term =
    BoolOr
        { symbol :: !Symbol
        , operand1, operand2 :: !term
        }

{- | Match the @BOOL.or@ hooked symbol.
 -}
matchBoolOr :: TermLike variable -> Maybe (BoolOr (TermLike variable))
matchBoolOr (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == orKey)
    return BoolOr { symbol, operand1, operand2 }
matchBoolOr _ = Nothing

{- | The @BOOL.not@ hooked symbol applied to a @term@-type argument.
 -}
data BoolNot term =
    BoolNot
        { symbol  :: !Symbol
        , operand :: !term
        }

{- | Match the @BOOL.not@ hooked symbol.
 -}
matchBoolNot :: TermLike variable -> Maybe (BoolNot (TermLike variable))
matchBoolNot (App_ symbol [operand]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == notKey)
    return BoolNot { symbol, operand }
matchBoolNot _ = Nothing

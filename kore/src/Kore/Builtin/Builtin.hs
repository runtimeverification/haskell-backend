{- |
Module      : Kore.Builtin.Builtin
Description : Built-in sort, symbol, and pattern verifiers
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Builtin as Builtin
@
 -}
module Kore.Builtin.Builtin
    ( Function
    , FunctionImplementation
      -- * Implementing builtin functions
    , notImplemented
    , unaryOperator
    , binaryOperator
    , ternaryOperator
    , functionEvaluator
    , verifierBug
    , wrongArity
    , runParser
    , appliedFunction
    , lookupSymbol
    , lookupSymbolUnit
    , lookupSymbolElement
    , lookupSymbolConcat
    , isSymbol
    , isSort
    , toKey
    , getAttemptedAxiom
    , makeDomainValueTerm
    , makeDomainValuePattern
      -- * Implementing builtin unification
    , unifyEqualsUnsolved
    , module Kore.Builtin.Verifiers
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( MaybeT (..)
    , fromMaybe
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute.Sort
import qualified Kore.Attribute.Sort.Element as Attribute.Sort
import qualified Kore.Attribute.Sort.Unit as Attribute.Sort
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol (..)
    )
import Kore.Builtin.Error
import Kore.Builtin.Verifiers
import Kore.Error
    ( Error
    )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (MetadataTools)
    , SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.IndexedModule.Resolvers as IndexedModule
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import Kore.Internal.Pattern as Pattern
    ( fromTermLike
    , top
    , withCondition
    )
import Kore.Internal.Predicate
    ( makeEqualsPredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
    ( topTODO
    )
import Kore.Internal.TermLike as TermLike
import Kore.Sort
    ( predicateSort
    )
import {-# SOURCE #-} qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )
import Kore.Step.Simplification.SimplificationType as SimplificationType
    ( SimplificationType (..)
    )
import Kore.Step.Simplification.Simplify
    ( AttemptedAxiom (..)
    , AttemptedAxiomResults (AttemptedAxiomResults)
    , BuiltinAndAxiomSimplifier (BuiltinAndAxiomSimplifier)
    , MonadSimplify
    , SimplifierVariable
    , applicationAxiomSimplifier
    )
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify
    ( scatter
    )
import Kore.Unparser

type Function = BuiltinAndAxiomSimplifier

notImplemented :: Function
notImplemented =
    BuiltinAndAxiomSimplifier notImplemented0
  where
    notImplemented0 _ _ = pure NotApplicable

{- | Return the supplied pattern as an 'AttemptedAxiom'.

  No substitution or predicate is applied.

  See also: 'Pattern'
 -}
appliedFunction
    :: (Monad m, Ord variable)
    => Pattern variable
    -> m (AttemptedAxiom variable)
appliedFunction epat =
    return $ Applied AttemptedAxiomResults
        { results = OrPattern.fromPattern epat
        , remainders = OrPattern.bottom
        }

{- | Construct a builtin unary operator.

  The operand type may differ from the result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.

 -}
unaryOperator
    :: forall a b
    .   (forall variable. Text -> Builtin (TermLike variable) -> a)
    -- ^ Parse operand
    ->  (forall variable
        . InternalVariable variable => Sort -> b -> Pattern variable
        )
    -- ^ Render result as pattern with given sort
    -> Text
    -- ^ Builtin function name (for error messages)
    -> (a -> b)
    -- ^ Operation on builtin types
    -> Function
unaryOperator
    extractVal
    asPattern
    ctx
    op
  =
    functionEvaluator unaryOperator0
  where
    get :: Builtin (TermLike variable) -> a
    get = extractVal ctx
    unaryOperator0
        :: InternalVariable variable
        => MonadSimplify m
        => Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    unaryOperator0 resultSort children =
        case Cofree.tailF . Recursive.project <$> children of
            [BuiltinF a] -> do
                -- Apply the operator to a domain value
                let r = op (get a)
                (appliedFunction . asPattern resultSort) r
            [_] -> return NotApplicable
            _ -> wrongArity (Text.unpack ctx)

{- | Construct a builtin binary operator.

  Both operands have the same builtin type, which may be different from the
  result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.

 -}
binaryOperator
    :: forall a b
    .  (forall variable. Text -> Builtin (TermLike variable) -> a)
    -- ^ Extract domain value
    ->  (forall variable
        . InternalVariable variable => Sort -> b -> Pattern variable
        )
    -- ^ Render result as pattern with given sort
    -> Text
    -- ^ Builtin function name (for error messages)
    -> (a -> a -> b)
    -- ^ Operation on builtin types
    -> Function
binaryOperator
    extractVal
    asPattern
    ctx
    op
  =
    functionEvaluator binaryOperator0
  where
    get :: Builtin (TermLike variable) -> a
    get = extractVal ctx
    binaryOperator0
        :: SimplifierVariable variable
        => MonadSimplify m
        => Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    binaryOperator0 resultSort children =
        case Cofree.tailF . Recursive.project <$> children of
            [BuiltinF a, BuiltinF b] -> do
                -- Apply the operator to two domain values
                let r = op (get a) (get b)
                (appliedFunction . asPattern resultSort) r
            [_, _] -> return NotApplicable
            _ -> wrongArity (Text.unpack ctx)

{- | Construct a builtin ternary operator.

  All three operands have the same builtin type, which may be different from the
  result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.

 -}
ternaryOperator
    :: forall a b
    .  (forall variable. Text -> Builtin (TermLike variable) -> a)
    -- ^ Extract domain value
    ->  (forall variable
        . InternalVariable variable => Sort -> b -> Pattern variable
        )
    -- ^ Render result as pattern with given sort
    -> Text
    -- ^ Builtin function name (for error messages)
    -> (a -> a -> a -> b)
    -- ^ Operation on builtin types
    -> Function
ternaryOperator
    extractVal
    asPattern
    ctx
    op
  =
    functionEvaluator ternaryOperator0
  where
    get :: Builtin (TermLike variable) -> a
    get = extractVal ctx
    ternaryOperator0
        :: SimplifierVariable variable
        => MonadSimplify m
        => Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    ternaryOperator0 resultSort children =
        case Cofree.tailF . Recursive.project <$> children of
            [ BuiltinF a, BuiltinF b, BuiltinF c ] -> do
                -- Apply the operator to three domain values
                let r = op (get a) (get b) (get c)
                (appliedFunction . asPattern resultSort) r
            [_, _, _] -> return NotApplicable
            _ -> wrongArity (Text.unpack ctx)

type FunctionImplementation
    = forall variable simplifier
        .  SimplifierVariable variable
        => MonadSimplify simplifier
        => Sort
        -> [TermLike variable]
        -> simplifier (AttemptedAxiom variable)

functionEvaluator :: FunctionImplementation -> Function
functionEvaluator impl =
    applicationAxiomSimplifier evaluator
  where
    evaluator
        :: SimplifierVariable variable
        => MonadSimplify simplifier
        => CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> simplifier (AttemptedAxiom variable)
    evaluator (valid :< app) =
        impl resultSort
        $ fmap TermLike.removeEvaluated applicationChildren
      where
        Application { applicationChildren } = app
        Attribute.Pattern { Attribute.patternSort = resultSort } = valid

{- | Run a parser on a verified domain value.

    Any parse failure indicates a bug in the well-formedness checker; in this
    case an error is thrown.

 -}
runParser :: HasCallStack => Text -> Either (Error e) a -> a
runParser ctx result =
    case result of
        Left e ->
            verifierBug $ Text.unpack ctx ++ ": " ++ Kore.Error.printError e
        Right a -> a

{- | Look up the symbol hooked to the named builtin in the provided module.
 -}
lookupSymbol
    :: Text
    -- ^ builtin name
    -> Sort
    -- ^ the hooked sort
    -> VerifiedModule Attribute.Symbol axiomAtts
    -> Either (Error e) Symbol
lookupSymbol builtinName builtinSort indexedModule = do
    symbolConstructor <-
        IndexedModule.resolveHook indexedModule builtinName builtinSort
    (symbolAttributes, sentenceSymbol) <-
        IndexedModule.resolveSymbol indexedModule symbolConstructor
    symbolSorts <- symbolOrAliasSorts [] sentenceSymbol
    return Symbol
        { symbolConstructor
        , symbolParams = []
        , symbolAttributes
        , symbolSorts
        }

{- | Find the symbol hooked to @unit@.

It is an error if the sort does not provide a @unit@ attribute; this is checked
during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolUnit
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolUnit tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    unit = Attribute.unit (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getUnit unit
        & fromMaybe missingUnitAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingUnitAttribute =
        verifierBug
        $ "missing 'unit' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Find the symbol hooked to @element@.

It is an error if the sort does not provide a @element@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolElement
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolElement tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    element = Attribute.element (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getElement element
        & fromMaybe missingElementAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingElementAttribute =
        verifierBug
        $ "missing 'element' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Find the symbol hooked to @concat@.

It is an error if the sort does not provide a @concat@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolConcat
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolConcat tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    concat' = Attribute.concat (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getConcat concat'
        & fromMaybe missingConcatAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingConcatAttribute =
        verifierBug
        $ "missing 'concat' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Is the given symbol hooked to the named builtin?
 -}
isSymbol
    :: Text  -- ^ Builtin symbol
    -> Symbol  -- ^ Kore symbol
    -> Bool
isSymbol builtinName Symbol { symbolAttributes = Attribute.Symbol { hook } } =
    getHook hook == Just builtinName

{- | Is the given sort hooked to the named builtin?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isSort :: Text -> SmtMetadataTools attr -> Sort -> Maybe Bool
isSort builtinName tools sort
  | isPredicateSort            = Nothing
  | SortVariableSort _ <- sort = Nothing
  | otherwise                  = Just (getHook hook == Just builtinName)
  where
    MetadataTools {sortAttributes} = tools
    Attribute.Sort {hook} = sortAttributes sort
    isPredicateSort = sort == predicateSort


{- | Ensure that a 'TermLike' is a concrete, normalized term.

If the pattern is not concrete and normalized, the function is
See also: 'Kore.Proof.Value.Value'

 -}
toKey :: TermLike variable -> Maybe (TermLike Concrete)
toKey purePattern = do
    p <- TermLike.asConcrete purePattern
    -- TODO (thomas.tuegel): Use the return value as the term.
    if TermLike.isConstructorLike p
        then return p
        else Nothing

{- | Run a function evaluator that can terminate early.
 -}
getAttemptedAxiom
    :: Monad m
    => MaybeT m (AttemptedAxiom variable)
    -> m (AttemptedAxiom variable)
getAttemptedAxiom attempt =
    fromMaybe NotApplicable <$> runMaybeT attempt

-- | Return an unsolved unification problem.
unifyEqualsUnsolved
    :: (MonadUnify unifier, SimplifierVariable variable)
    => SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
unifyEqualsUnsolved SimplificationType.And a b = do
    let unified = TermLike.markSimplified $ mkAnd a b
    orCondition <- Ceil.makeEvaluateTerm SideCondition.topTODO unified
    predicate <- Monad.Unify.scatter orCondition
    return (unified `Pattern.withCondition` predicate)
unifyEqualsUnsolved SimplificationType.Equals a b =
    return Pattern.top
        {predicate = Predicate.markSimplified $ makeEqualsPredicate_ a b}

makeDomainValueTerm
    :: InternalVariable variable
    => Sort
    -> Text
    -> TermLike variable
makeDomainValueTerm sort stringLiteral =
    mkDomainValue DomainValue
        { domainValueSort = sort
        , domainValueChild = mkStringLiteral stringLiteral
        }

makeDomainValuePattern
    :: InternalVariable variable
    => Sort
    -> Text
    -> Pattern variable
makeDomainValuePattern sort stringLiteral =
    Pattern.fromTermLike
    $ makeDomainValueTerm sort stringLiteral

{- |
Module      : Kore.Builtin.Builtin
Description : Built-in sort, symbol, and pattern verifiers
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Builtin as Builtin
@
-}
module Kore.Builtin.Builtin (
    Function,

    -- * Implementing builtin functions
    notImplemented,
    unaryOperator,
    binaryOperator,
    ternaryOperator,
    functionEvaluator,
    applicationEvaluator,
    verifierBug,
    wrongArity,
    runParser,
    appliedFunction,
    lookupSymbol,
    lookupSymbolUnit,
    lookupSymbolElement,
    lookupSymbolConcat,
    isSymbol,
    isSort,
    getAttemptedAxiom,
    makeDomainValueTerm,
    makeDomainValuePattern,

    -- * Implementing builtin unification
    module Kore.Builtin.Verifiers,
) where

import Control.Error (
    MaybeT (..),
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Kore.Attribute.Hook (
    Hook (..),
 )
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute.Sort
import qualified Kore.Attribute.Sort.Element as Attribute.Sort
import qualified Kore.Attribute.Sort.Unit as Attribute.Sort
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol (..),
 )
import Kore.Builtin.Error
import Kore.Builtin.Verifiers
import Kore.Error (
    Error,
 )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.IndexedModule.MetadataTools (
    MetadataTools (MetadataTools),
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.IndexedModule.Resolvers as IndexedModule
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern as Pattern (
    fromTermLike,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike as TermLike
import Kore.Sort (
    predicateSort,
 )
import Kore.Step.Simplification.Simplify (
    AttemptedAxiom (..),
    AttemptedAxiomResults (AttemptedAxiomResults),
    BuiltinAndAxiomSimplifier (BuiltinAndAxiomSimplifier),
    MonadSimplify,
    applicationAxiomSimplifier,
 )
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults (
    AttemptedAxiomResults (..),
 )
import Kore.Unparser
import Prelude.Kore

-- TODO (thomas.tuegel): Include hook name here.

notImplemented :: BuiltinAndAxiomSimplifier
notImplemented =
    BuiltinAndAxiomSimplifier notImplemented0
  where
    notImplemented0 _ _ = pure NotApplicable

{- | Return the supplied pattern as an 'AttemptedAxiom'.

  No substitution or predicate is applied.

  See also: 'Pattern'
-}
appliedFunction ::
    (Monad m, InternalVariable variable) =>
    Pattern variable ->
    m (AttemptedAxiom variable)
appliedFunction epat =
    return $
        Applied
            AttemptedAxiomResults
                { results = OrPattern.fromPattern epat
                , remainders = OrPattern.bottom
                }

{- | Construct a builtin unary operator.

  The operand type may differ from the result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.
-}
unaryOperator ::
    forall a b.
    -- | Parse operand
    (forall variable. Text -> TermLike variable -> Maybe a) ->
    -- | Render result as pattern with given sort
    ( forall variable.
      InternalVariable variable =>
      Sort ->
      b ->
      Pattern variable
    ) ->
    -- | Builtin function name (for error messages)
    Text ->
    -- | Operation on builtin types
    (a -> b) ->
    BuiltinAndAxiomSimplifier
unaryOperator extractVal asPattern ctx op =
    functionEvaluator unaryOperator0
  where
    get :: TermLike variable -> Maybe a
    get = extractVal ctx

    unaryOperator0 :: Function
    unaryOperator0 _ resultSort children =
        case children of
            [termLike]
                | Just a <- get termLike -> do
                    -- Apply the operator to a domain value
                    let r = op a
                    return (asPattern resultSort r)
                | otherwise -> empty
            _ -> wrongArity (Text.unpack ctx)

{- | Construct a builtin binary operator.

  Both operands have the same builtin type, which may be different from the
  result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.
-}
binaryOperator ::
    forall a b.
    -- | Extract domain value
    (forall variable. Text -> TermLike variable -> Maybe a) ->
    -- | Render result as pattern with given sort
    ( forall variable.
      InternalVariable variable =>
      Sort ->
      b ->
      Pattern variable
    ) ->
    -- | Builtin function name (for error messages)
    Text ->
    -- | Operation on builtin types
    (a -> a -> b) ->
    BuiltinAndAxiomSimplifier
binaryOperator extractVal asPattern ctx op =
    functionEvaluator binaryOperator0
  where
    get :: TermLike variable -> Maybe a
    get = extractVal ctx

    binaryOperator0 :: Function
    binaryOperator0 _ resultSort children =
        case children of
            [get -> Just a, get -> Just b] -> do
                -- Apply the operator to two domain values
                let r = op a b
                return (asPattern resultSort r)
            [_, _] -> empty
            _ -> wrongArity (Text.unpack ctx)

{- | Construct a builtin ternary operator.

  All three operands have the same builtin type, which may be different from the
  result type.

  The function is skipped if its arguments are not domain values.
  It is an error if the wrong number of arguments is given; this must be checked
  during verification.
-}
ternaryOperator ::
    forall a b.
    -- | Extract domain value
    (forall variable. Text -> TermLike variable -> Maybe a) ->
    -- | Render result as pattern with given sort
    ( forall variable.
      InternalVariable variable =>
      Sort ->
      b ->
      Pattern variable
    ) ->
    -- | Builtin function name (for error messages)
    Text ->
    -- | Operation on builtin types
    (a -> a -> a -> b) ->
    BuiltinAndAxiomSimplifier
ternaryOperator extractVal asPattern ctx op =
    functionEvaluator ternaryOperator0
  where
    get :: TermLike variable -> Maybe a
    get = extractVal ctx

    ternaryOperator0 :: Function
    ternaryOperator0 _ resultSort children =
        case children of
            [get -> Just a, get -> Just b, get -> Just c] -> do
                -- Apply the operator to three domain values
                let r = op a b c
                return (asPattern resultSort r)
            [_, _, _] -> empty
            _ -> wrongArity (Text.unpack ctx)

type Function =
    forall variable simplifier.
    InternalVariable variable =>
    HasCallStack =>
    MonadSimplify simplifier =>
    SideCondition variable ->
    Sort ->
    [TermLike variable] ->
    MaybeT simplifier (Pattern variable)

functionEvaluator :: Function -> BuiltinAndAxiomSimplifier
functionEvaluator impl =
    applicationEvaluator $ \sideCondition app -> do
        let Application{applicationSymbolOrAlias = symbol} = app
            Application{applicationChildren = args} = app
            resultSort = symbolSorts symbol & applicationSortsResult
        impl sideCondition resultSort args

applicationEvaluator ::
    ( forall variable simplifier.
      InternalVariable variable =>
      MonadSimplify simplifier =>
      SideCondition variable ->
      Application Symbol (TermLike variable) ->
      MaybeT simplifier (Pattern variable)
    ) ->
    BuiltinAndAxiomSimplifier
applicationEvaluator impl =
    applicationAxiomSimplifier evaluator
  where
    evaluator ::
        InternalVariable variable =>
        MonadSimplify simplifier =>
        SideCondition variable ->
        CofreeF
            (Application Symbol)
            (TermAttributes variable)
            (TermLike variable) ->
        simplifier (AttemptedAxiom variable)
    evaluator sideCondition (_ :< app) = do
        getAttemptedAxiom
            (impl sideCondition app >>= appliedFunction)

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

-- | Look up the symbol hooked to the named builtin in the provided module.
lookupSymbol ::
    -- | builtin name
    Text ->
    -- | the hooked sort
    Sort ->
    VerifiedModule Attribute.Symbol ->
    Either (Error e) Symbol
lookupSymbol builtinName builtinSort indexedModule = do
    symbolConstructor <-
        IndexedModule.resolveHook indexedModule builtinName builtinSort
    (symbolAttributes, sentenceSymbol) <-
        IndexedModule.resolveSymbol indexedModule symbolConstructor
    symbolSorts <- symbolOrAliasSorts [] sentenceSymbol
    return
        Symbol
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
lookupSymbolUnit ::
    SmtMetadataTools Attribute.Symbol ->
    Sort ->
    Symbol
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
    ~missingUnitAttribute =
        verifierBug $
            "missing 'unit' attribute of sort '"
                ++ unparseToString builtinSort
                ++ "'"

{- | Find the symbol hooked to @element@.

It is an error if the sort does not provide a @element@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.
-}

-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolElement ::
    SmtMetadataTools Attribute.Symbol ->
    Sort ->
    Symbol
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
    ~missingElementAttribute =
        verifierBug $
            "missing 'element' attribute of sort '"
                ++ unparseToString builtinSort
                ++ "'"

{- | Find the symbol hooked to @concat@.

It is an error if the sort does not provide a @concat@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.
-}

-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolConcat ::
    SmtMetadataTools Attribute.Symbol ->
    Sort ->
    Symbol
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
    ~missingConcatAttribute =
        verifierBug $
            "missing 'concat' attribute of sort '"
                ++ unparseToString builtinSort
                ++ "'"

-- | Is the given symbol hooked to the named builtin?
isSymbol ::
    -- | Builtin symbol
    Text ->
    -- | Kore symbol
    Symbol ->
    Bool
isSymbol builtinName Symbol{symbolAttributes = Attribute.Symbol{hook}} =
    getHook hook == Just builtinName

{- | Is the given sort hooked to the named builtin?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isSort :: Text -> SmtMetadataTools attr -> Sort -> Maybe Bool
isSort builtinName tools sort
    | isPredicateSort = Nothing
    | SortVariableSort _ <- sort = Nothing
    | otherwise =
        let MetadataTools{sortAttributes} = tools
            Attribute.Sort{hook} = sortAttributes sort
         in Just (getHook hook == Just builtinName)
  where
    isPredicateSort = sort == predicateSort

-- | Run a function evaluator that can terminate early.
getAttemptedAxiom ::
    Monad m =>
    MaybeT m (AttemptedAxiom variable) ->
    m (AttemptedAxiom variable)
getAttemptedAxiom attempt =
    fromMaybe NotApplicable <$> runMaybeT attempt

makeDomainValueTerm ::
    InternalVariable variable =>
    Sort ->
    Text ->
    TermLike variable
makeDomainValueTerm sort stringLiteral =
    mkDomainValue
        DomainValue
            { domainValueSort = sort
            , domainValueChild = mkStringLiteral stringLiteral
            }

makeDomainValuePattern ::
    InternalVariable variable =>
    Sort ->
    Text ->
    Pattern variable
makeDomainValuePattern sort stringLiteral =
    Pattern.fromTermLike $
        makeDomainValueTerm sort stringLiteral

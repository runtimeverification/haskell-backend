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
    (
      -- * Using builtin verifiers
      Verifiers (..)
    , SymbolVerifier (..), SymbolVerifiers
    , SortDeclVerifier, SortDeclVerifiers
    , DomainValueVerifier, DomainValueVerifiers
    , SortVerifier (..)
    , Function
    , Parser
    , symbolVerifier
    , sortDeclVerifier
      -- * Smart constructors for DomainValueVerifier
    , makeEncodedDomainValueVerifier
      -- * Declaring builtin verifiers
    , verifySortDecl
    , getUnitId
    , getElementId
    , getConcatId
    , assertSymbolHook
    , assertSymbolResultSort
    , verifySort
    , verifySortHasDomainValues
    , expectDomainValue
    , acceptAnySort
    , verifySymbol
    , verifySymbolArguments
    , verifyDomainValue
    , parseString
      -- * Implementing builtin functions
    , notImplemented
    , unaryOperator
    , binaryOperator
    , ternaryOperator
    , FunctionImplementation
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
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( MaybeT (..)
    , fromMaybe
    )
import Control.Monad
    ( zipWithM_
    )
import qualified Control.Monad as Monad
import Data.Function
import qualified Data.Functor.Foldable as Recursive
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Void
    ( Void
    )
import GHC.Stack
    ( HasCallStack
    )
import Text.Megaparsec
    ( Parsec
    )
import qualified Text.Megaparsec as Parsec

import qualified Kore.AST.Error as Kore.Error
import qualified Kore.ASTVerifier.AttributesVerifier as Verifier.Attributes
import Kore.ASTVerifier.Error
    ( VerifyError
    )
import Kore.Attribute.Attributes
    ( Attributes (..)
    )
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute.Sort
import qualified Kore.Attribute.Sort.Element as Attribute.Sort
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute
import qualified Kore.Attribute.Sort.Unit as Attribute.Sort
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Builtin.Error
import Kore.Error
    ( Error
    )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule
    ( IndexedModule
    , VerifiedModule
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
    )
import Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    , makeEqualsPredicate
    )
import qualified Kore.Proof.Value as Value
import Kore.Sort
    ( predicateSort
    )
import Kore.Step.Simplification.SimplificationType as SimplificationType
    ( SimplificationType (..)
    )
import Kore.Step.Simplification.Simplify
    ( AttemptedAxiom (..)
    , AttemptedAxiomResults (AttemptedAxiomResults)
    , BuiltinAndAxiomSimplifier (BuiltinAndAxiomSimplifier)
    , BuiltinAndAxiomSimplifierMap
    , MonadSimplify
    , TermLikeSimplifier
    , applicationAxiomSimplifier
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import Kore.Syntax.Definition
    ( ParsedSentenceSort
    , ParsedSentenceSymbol
    , SentenceSort (..)
    , SentenceSymbol (..)
    )
import Kore.Unparser
import qualified Kore.Verified as Verified

-- TODO (thomas.tuegel): Split up verifiers and evaluators.

type Parser = Parsec Void Text

type Function = BuiltinAndAxiomSimplifier

-- | Verify a sort declaration.
type SortDeclVerifier =
        VerifiedModule Attribute.Symbol Attribute.Axiom
    -- ^ Indexed module, to look up sort declarations
    ->  ParsedSentenceSort
    -- ^ Sort declaration to verify
    ->  Attribute.Sort
    -- ^ Declared sort attributes
    ->  Either (Error VerifyError) ()

newtype SortVerifier =
    SortVerifier
        { runSortVerifier
            :: forall patternType
            .  (Id -> Either (Error VerifyError) (SentenceSort patternType))
            -> Sort
            -> Either (Error VerifyError) ()
        }

-- | @SortDeclVerifiers@ associates a sort verifier with its builtin sort name.
type SortDeclVerifiers = HashMap Text SortDeclVerifier

newtype SymbolVerifier =
    SymbolVerifier
        { runSymbolVerifier
            :: forall patternType
            .  (Id -> Either (Error VerifyError) (SentenceSort patternType))
            -> ParsedSentenceSymbol
            -> Either (Error VerifyError) ()
        }

{- | @SymbolVerifiers@ associates a @SymbolVerifier@ with each builtin
  symbol name.
 -}
type SymbolVerifiers = HashMap Text SymbolVerifier

{- | @DomainValueVerifier@ verifies a domain value and returns the modified
  represention parameterized over @m@, the verification monad.

-}
type DomainValueVerifier child =
       DomainValue Sort child -> Either (Error VerifyError) (Builtin child)

-- | @DomainValueVerifiers@  associates a @DomainValueVerifier@ with each
-- builtin
type DomainValueVerifiers child = (HashMap Text (DomainValueVerifier child))


{- | Verify builtin sorts, symbols, and patterns.
 -}
data Verifiers = Verifiers
    { sortDeclVerifiers    :: SortDeclVerifiers
    , symbolVerifiers      :: SymbolVerifiers
    , domainValueVerifiers :: DomainValueVerifiers Verified.Pattern
    }

{- | Look up and apply a builtin sort declaration verifier.

The 'Hook' name should refer to a builtin sort; if it is unset or the name is
not recognized, verification succeeds.

 -}
sortDeclVerifier :: Verifiers -> Hook -> SortDeclVerifier
sortDeclVerifier Verifiers { sortDeclVerifiers } hook =
    let
        hookedSortVerifier = do
            -- Get the builtin sort name.
            sortName <- getHook hook
            HashMap.lookup sortName sortDeclVerifiers
    in
        fromMaybe
            -- There is nothing to verify because either
            -- 1. the sort is not hooked, or
            -- 2. there is no SortVerifier registered to the hooked name.
            -- In either case, there is nothing more to do.
            (\_ _ _ -> pure ())
            -- Invoke the verifier that is registered to this builtin sort.
            hookedSortVerifier

{- | Look up and apply a builtin symbol verifier.

The 'Hook' name should refer to a builtin symbol; if it is unset or the name is
not recognized, verification succeeds.

 -}
symbolVerifier :: Verifiers -> Hook -> SymbolVerifier
symbolVerifier Verifiers { symbolVerifiers } hook =
    let
        hookedSymbolVerifier = do
            -- Get the builtin sort name.
            symbolName <- getHook hook
            HashMap.lookup symbolName symbolVerifiers
    in
        fromMaybe
            -- There is nothing to verify because either
            -- 1. the symbol is not hooked, or
            -- 2. there is no SymbolVerifier registered to the hooked name.
            -- In either case, there is nothing more to do.
            (SymbolVerifier $ \_ _ -> pure ())
            -- Invoke the verifier that is registered to this builtin symbol.
            hookedSymbolVerifier

notImplemented :: Function
notImplemented =
    BuiltinAndAxiomSimplifier notImplemented0
  where
    notImplemented0 _ _ _ _ = pure NotApplicable

{- | Verify a builtin sort declaration.

  Check that the hooked sort does not take any sort parameters.

 -}
verifySortDecl :: SortDeclVerifier
verifySortDecl _ SentenceSort { sentenceSortParameters } _ =
    getZeroParams sentenceSortParameters

{- | Throw a 'VerifyError' if there are any sort parameters.
 -}
getZeroParams :: [SortVariable] -> Either (Error VerifyError) ()
getZeroParams =
    \case
        [] -> return ()
        params ->
            Kore.Error.koreFail
                ("Expected 0 sort parameters, found " ++ show (length params))

{- | Get the identifier of the @unit@ sort attribute.

Fail if the attribute is missing.

 -}
getUnitId
    :: Attribute.Sort
    -- ^ Sort attributes
    -> Either (Error VerifyError) Id
getUnitId Attribute.Sort { unit = Attribute.Sort.Unit sortUnit } =
    case sortUnit of
        Just SymbolOrAlias { symbolOrAliasConstructor } ->
            return symbolOrAliasConstructor
        Nothing -> Kore.Error.koreFail "Missing 'unit' attribute."

{- | Get the identifier of the @element@ sort attribute.

Fail if the attribute is missing.

 -}
getElementId
    :: Attribute.Sort
    -- ^ Sort attributes
    -> Either (Error VerifyError) Id
getElementId Attribute.Sort { element = Attribute.Sort.Element sortElement } =
    case sortElement of
        Just SymbolOrAlias { symbolOrAliasConstructor } ->
            return symbolOrAliasConstructor
        Nothing -> Kore.Error.koreFail "Missing 'element' attribute."

{- | Get the identifier of the @concat@ sort attribute.

Fail if the attribute is missing.

 -}
getConcatId
    :: Attribute.Sort
    -- ^ Sort attributes
    -> Either (Error VerifyError) Id
getConcatId Attribute.Sort { concat = Attribute.Sort.Concat sortConcat } =
    case sortConcat of
        Just SymbolOrAlias { symbolOrAliasConstructor } ->
            return symbolOrAliasConstructor
        Nothing -> Kore.Error.koreFail "Missing 'concat' attribute."

{- | Check that the symbol's @hook@ attribute matches the expected value.

Fail if the symbol is not defined or the attribute is missing.

 -}
assertSymbolHook
    :: IndexedModule patternType declAttrs axiomAttrs
    -> Id
    -- ^ Symbol identifier
    -> Text
    -- ^ Expected hook
    -> Either (Error VerifyError) ()
assertSymbolHook indexedModule symbolId expected = do
    (_, decl) <- IndexedModule.resolveSymbol indexedModule symbolId
    let
        SentenceSymbol { sentenceSymbolAttributes = attrs } = decl
        SentenceSymbol { sentenceSymbolSymbol = symbol } = decl
    Hook { getHook } <- Verifier.Attributes.parseAttributes attrs
    case getHook of
        Just hook
          | hook == expected -> return ()
          | otherwise ->
            Kore.Error.koreFailWithLocations
                [symbol]
                ("Symbol is not hooked to builtin symbol '" <> expected <> "'")
        Nothing ->
            Kore.Error.koreFailWithLocations
                [symbol]
                "Missing 'hook' attribute"

{- | Check that the symbol's result sort matches the expected value.

Fail if the symbol is not defined.

 -}
assertSymbolResultSort
    :: IndexedModule patternType declAttrs axiomAttrs
    -> Id
    -- ^ Symbol identifier
    -> Sort
    -- ^ Expected result sort
    -> Either (Error VerifyError) ()
assertSymbolResultSort indexedModule symbolId expectedSort = do
    (_, decl) <- IndexedModule.resolveSymbol indexedModule symbolId
    let
        SentenceSymbol { sentenceSymbolResultSort = actualSort } = decl
        SentenceSymbol { sentenceSymbolSymbol = symbol } = decl
    Monad.unless (actualSort == expectedSort)
        $ Kore.Error.koreFailWithLocations
            [symbol]
            ("Symbol does not return sort '"
                <> unparseToText expectedSort <> "'")

{- | Verify the occurrence of a builtin sort.

  Check that the sort is hooked to the named builtin. The sort parameters are
  already checked by the verifier.

 -}
verifySort
    :: Text
    -> SortVerifier
verifySort builtinName =
    SortVerifier worker
  where
    worker
        :: forall patternType
        .  (Id -> Either (Error VerifyError) (SentenceSort patternType))
        -> Sort
        -> Either (Error VerifyError) ()
    worker findSort (SortActualSort SortActual { sortActualName }) = do
        SentenceSort { sentenceSortAttributes } <- findSort sortActualName
        let expectHook = Hook (Just builtinName)
        declHook <- Verifier.Attributes.parseAttributes sentenceSortAttributes
        Kore.Error.koreFailWhen (expectHook /= declHook)
            ("Sort '" ++ getIdForError sortActualName
                ++ "' is not hooked to builtin sort '"
                ++ Text.unpack builtinName ++ "'")
    worker _ (SortVariableSort SortVariable { getSortVariable }) =
        Kore.Error.koreFail
            ("unexpected sort variable '"
                ++ getIdForError getSortVariable ++ "'")

-- Verify a sort by only checking if it has domain values.
verifySortHasDomainValues :: SortVerifier
verifySortHasDomainValues = SortVerifier worker
  where
    worker
        :: forall patternType
        .  (Id -> Either (Error VerifyError) (SentenceSort patternType))
        -> Sort
        -> Either (Error VerifyError) ()
    worker findSort (SortActualSort SortActual { sortActualName }) = do
        SentenceSort { sentenceSortAttributes } <- findSort sortActualName
        sortAttr <- parseSortAttributes sentenceSortAttributes
        let hasDomainValues =
                Attribute.getHasDomainValues
                . Attribute.hasDomainValues
                $ sortAttr
        Kore.Error.koreFailWhen (not hasDomainValues)
            ("Sort '" ++ getIdForError sortActualName
                ++ "' does not have domain values.")
    worker _ (SortVariableSort SortVariable { getSortVariable }) =
        Kore.Error.koreFail
            ("unexpected sort variable '"
                ++ getIdForError getSortVariable ++ "'")
    parseSortAttributes
        :: Attributes
        -> Either (Error VerifyError) Attribute.Sort
    parseSortAttributes rawSortAttributes =
        Attribute.Parser.liftParser
        $ Attribute.Parser.parseAttributes rawSortAttributes

expectDomainValue
    :: Monad m
    => Text
    -- ^ Context for error message
    -> TermLike variable
    -- ^ Operand pattern
    -> MaybeT m Text
expectDomainValue ctx =
    \case
        DV_ _ child ->
            case child of
                StringLiteral_ text ->
                    return text
                _ ->
                    verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a string literal"
        _ -> empty

-- | Wildcard for sort verification on parameterized builtin sorts
acceptAnySort :: SortVerifier
acceptAnySort = SortVerifier $ \_ _ -> return ()

{- | Find the hooked sort for a domain value sort. -}
lookupHookSort
    :: (Id -> Either (Error VerifyError) (SentenceSort patternType))
    -> Sort
    -> Either (Error VerifyError) (Maybe Text)
lookupHookSort findSort (SortActualSort SortActual { sortActualName }) = do
    SentenceSort { sentenceSortAttributes } <- findSort sortActualName
    Hook mHookSort <- Verifier.Attributes.parseAttributes sentenceSortAttributes
    return mHookSort
lookupHookSort _ (SortVariableSort SortVariable { getSortVariable }) =
    Kore.Error.koreFail
        ("unexpected sort variable '" ++ getIdForError getSortVariable ++ "'")

{- | Verify a builtin symbol declaration.

  The declared sorts must match the builtin sorts.

  See also: 'verifySymbolArguments'

 -}
verifySymbol
    :: SortVerifier  -- ^ Builtin result sort
    -> [SortVerifier]  -- ^ Builtin argument sorts
    -> SymbolVerifier
verifySymbol verifyResult verifyArguments =
    SymbolVerifier $ \findSort decl -> do
        let SentenceSymbol { sentenceSymbolResultSort = result } = decl
        Kore.Error.withContext "In result sort"
            (runSortVerifier verifyResult findSort result)
        runSymbolVerifier (verifySymbolArguments verifyArguments) findSort decl

{- | Verify the arguments of a builtin sort declaration.

  The declared argument sorts must match the builtin argument
  sorts. @verifySymbolArguments@ only checks the symbol's argument sorts; use
  'verifySymbol' if it is also necessary to check the symbol's result sort.

  See also: 'verifySymbol'

 -}
verifySymbolArguments
    :: [SortVerifier]  -- ^ Builtin argument sorts
    -> SymbolVerifier
verifySymbolArguments verifyArguments =
    SymbolVerifier $ \findSort sentenceSymbol ->
        Kore.Error.withContext "In argument sorts" $ do
            let SentenceSymbol { sentenceSymbolSorts = sorts } = sentenceSymbol
                builtinArity = length verifyArguments
                arity = length sorts
            Kore.Error.koreFailWhen (arity /= builtinArity)
                ("Expected " ++ show builtinArity
                ++ " arguments, found " ++ show arity)
            zipWithM_ (\verify sort -> verify findSort sort)
                (runSortVerifier <$> verifyArguments)
                sorts

{- | Run a DomainValueVerifier.
-}
verifyDomainValue
    :: DomainValueVerifiers (TermLike variable)
    -> (Id -> Either (Error VerifyError) (SentenceSort patternType))
    -> DomainValue Sort (TermLike variable)
    -> Either (Error VerifyError) (TermLikeF variable (TermLike variable))
verifyDomainValue
    verifiers
    findSort
    domain
  =
    case domainValueSort of
        SortActualSort _ -> do
            hookSort <- lookupHookSort findSort domainValueSort
            fromMaybe (external domain) $ do
                hook <- hookSort
                verifier <- HashMap.lookup hook verifiers
                let context =
                        "Verifying builtin sort '" ++ Text.unpack hook ++ "'"
                    verify = Kore.Error.withContext context . verifier
                pure (BuiltinF <$> verify domain)
        SortVariableSort _ -> external domain
  where
    external = return . DomainValueF
    DomainValue { domainValueSort } = domain

-- | Construct a 'DomainValueVerifier' for an encodable sort.
makeEncodedDomainValueVerifier
    :: Text
    -- ^ Builtin sort identifier
    -> (DomainValue Sort child -> Either (Error VerifyError) (Builtin child))
    -- ^ encoding function for the builtin sort
    -> DomainValueVerifier child
makeEncodedDomainValueVerifier _builtinSort encodeSort domain =
    Kore.Error.withContext "While parsing domain value"
        (encodeSort domain)

{- | Run a parser on a string.

 -}
parseString
    :: Parser a
    -> Text
    -> Either (Error VerifyError) a
parseString parser lit =
    let parsed = Parsec.parse (parser <* Parsec.eof) "<string literal>" lit
    in castParseError parsed
  where
    castParseError =
        either (Kore.Error.koreFail . Parsec.errorBundlePretty) pure

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
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    unaryOperator0 _ resultSort children =
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
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    binaryOperator0 _ resultSort children =
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
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    ternaryOperator0 _ resultSort children =
        case Cofree.tailF . Recursive.project <$> children of
            [ BuiltinF a, BuiltinF b, BuiltinF c ] -> do
                -- Apply the operator to three domain values
                let r = op (get a) (get b) (get c)
                (appliedFunction . asPattern resultSort) r
            [_, _, _] -> return NotApplicable
            _ -> wrongArity (Text.unpack ctx)

type FunctionImplementation
    = forall variable m
        .  SimplifierVariable variable
        => MonadSimplify m
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)

functionEvaluator :: FunctionImplementation -> Function
functionEvaluator impl =
    applicationAxiomSimplifier evaluator
  where
    evaluator
        :: SimplifierVariable variable
        => MonadSimplify simplifier
        => TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> simplifier (AttemptedAxiom variable)
    evaluator simplifier _axiomIdToSimplifier (valid :< app) =
        impl simplifier resultSort applicationChildren
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
    _ <- Value.fromTermLike p
    return p

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
    :: (Monad m, SimplifierVariable variable)
    => SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> m (Pattern variable)
unifyEqualsUnsolved SimplificationType.And a b =
    let
        unified = mkAnd a b
        predicate = makeCeilPredicate unified
    in
        return (pure unified) { predicate }
unifyEqualsUnsolved SimplificationType.Equals a b =
    return Pattern.top {predicate = makeEqualsPredicate a b}

makeDomainValueTerm
    :: InternalVariable variable
    => Sort
    -> Text
    -> TermLike variable
makeDomainValueTerm sort stringLiteral =
    mkDomainValue
    $ DomainValue
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

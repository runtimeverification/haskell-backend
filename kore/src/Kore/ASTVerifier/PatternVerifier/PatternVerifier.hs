{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.ASTVerifier.PatternVerifier.PatternVerifier
    ( PatternVerifier (..)
    , runPatternVerifier
    , Context (..)
    , verifiedModuleContext
    -- * Declared variables
    , DeclaredVariables (..), emptyDeclaredVariables
    , withDeclaredVariables
    , lookupDeclaredVariable
    , addDeclaredVariable
    , newDeclaredVariable
    , uniqueDeclaredVariables
    -- * Hooks
    , PatternVerifierHook (..)
    -- * Utilities
    , lookupSortDeclaration
    , lookupAlias
    , lookupSymbol
    , assertExpectedSort
    , assertSameSort
    ) where

import Prelude.Kore

import Control.Applicative
import Control.Monad
    ( (>=>)
    )
import Control.Monad.Reader
    ( MonadReader
    , ReaderT
    , runReaderT
    )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import Data.Text.Prettyprint.Doc
    ( (<+>)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Text.Prettyprint.Doc.Render.Text
    ( renderStrict
    )
import qualified GHC.Generics as GHC

import Kore.AST.Error
import Kore.ASTVerifier.Error
import Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import qualified Kore.Internal.Alias as Internal
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.Symbol as Internal
import Kore.Syntax as Syntax
import Kore.Syntax.Definition
import Kore.Unparser
import Kore.Variables.UnifiedVariable
import qualified Kore.Verified as Verified

newtype DeclaredVariables =
    DeclaredVariables
        { getDeclaredVariables :: Map.Map Id (UnifiedVariable Variable) }
    deriving (Monoid, Semigroup)

emptyDeclaredVariables :: DeclaredVariables
emptyDeclaredVariables = mempty

{- | 'PatternVerifierHook' is a hook run after verifying a 'Verified.Pattern'.

These are usually used to construct and verify internal representations after
parsing.

The 'Semigroup' instance is used to compose 'PatternVerifierHook's to be applied
in sequence.

 -}
newtype PatternVerifierHook =
    PatternVerifierHook
        { runPatternVerifierHook
            :: Verified.Pattern -> PatternVerifier Verified.Pattern
        }

instance Semigroup PatternVerifierHook where
    (<>) verifier1 verifier2 =
        PatternVerifierHook
            (Function.on (>=>) runPatternVerifierHook verifier1 verifier2)
    {-# INLINE (<>) #-}

instance Monoid PatternVerifierHook where
    mempty = PatternVerifierHook return
    {-# INLINE mempty #-}

data Context =
    Context
        { declaredVariables :: !DeclaredVariables
        , declaredSortVariables :: !(Set SortVariable)
        -- ^ The sort variables in scope.
        , indexedModule :: !(VerifiedModule Attribute.Symbol Attribute.Null)
        -- ^ The indexed Kore module containing all definitions in scope.
        , patternVerifierHook :: !PatternVerifierHook
        }
    deriving (GHC.Generic)

verifiedModuleContext :: VerifiedModule Attribute.Symbol axiomAttr -> Context
verifiedModuleContext verifiedModule =
    Context
        { declaredVariables = mempty
        , declaredSortVariables = mempty
        , indexedModule
        , patternVerifierHook = mempty
        }
  where
    indexedModule = eraseAxiomAttributes verifiedModule

newtype PatternVerifier a =
    PatternVerifier
        { getPatternVerifier :: ReaderT Context (Either (Error VerifyError)) a }
    deriving (Applicative, Functor, Monad)

deriving instance MonadReader Context PatternVerifier

deriving instance e ~ VerifyError => MonadError (Error e) PatternVerifier

runPatternVerifier
    :: Context
    -> PatternVerifier a
    -> Either (Error VerifyError) a
runPatternVerifier ctx PatternVerifier { getPatternVerifier } =
    runReaderT getPatternVerifier ctx

lookupSortDeclaration :: Id -> PatternVerifier Verified.SentenceSort
lookupSortDeclaration sortId = do
    Context { indexedModule } <- Reader.ask
    (_, sortDecl) <- resolveSort indexedModule sortId
    return sortDecl

lookupAlias :: SymbolOrAlias -> MaybeT PatternVerifier Verified.Alias
lookupAlias symbolOrAlias = do
    Context { indexedModule } <- Reader.ask
    let resolveAlias' = resolveAlias indexedModule aliasConstructor
    (_, decl) <- resolveAlias' `catchError` const empty
    aliasSorts <-
        Trans.lift
        $ applicationSortsFromSymbolOrAliasSentence symbolOrAlias decl
    let aliasLeft = leftDefinition decl
        aliasRight = sentenceAliasRightPattern decl
    return Internal.Alias
        { aliasConstructor
        , aliasParams
        , aliasSorts
        , aliasLeft
        , aliasRight
        }
  where
    aliasConstructor = symbolOrAliasConstructor symbolOrAlias
    aliasParams = symbolOrAliasParams symbolOrAlias
    leftDefinition def =
        applicationChildren
        . sentenceAliasLeftPattern
        $ def

lookupSymbol :: SymbolOrAlias -> MaybeT PatternVerifier Internal.Symbol
lookupSymbol symbolOrAlias = do
    Context { indexedModule } <- Reader.ask
    let resolveSymbol' = resolveSymbol indexedModule symbolConstructor
    (symbolAttributes, decl) <- resolveSymbol' `catchError` const empty
    symbolSorts <-
        Trans.lift
        $ applicationSortsFromSymbolOrAliasSentence symbolOrAlias decl
    let symbol =
            Internal.Symbol
                { symbolConstructor
                , symbolParams
                , symbolAttributes
                , symbolSorts
                }
    return symbol
  where
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias

lookupDeclaredVariable :: Id -> PatternVerifier (UnifiedVariable Variable)
lookupDeclaredVariable varId = do
    variables <- Reader.asks (getDeclaredVariables . declaredVariables)
    maybe errorUnquantified return $ Map.lookup varId variables
  where
    errorUnquantified :: PatternVerifier (UnifiedVariable Variable)
    errorUnquantified =
        koreFailWithLocations [varId]
            ("Unquantified variable: '" <> getId varId <> "'.")

addDeclaredVariable
    :: UnifiedVariable Variable
    -> DeclaredVariables
    -> DeclaredVariables
addDeclaredVariable variable (getDeclaredVariables -> variables) =
    DeclaredVariables $ Map.insert
        (foldMapVariable variableName variable)
        variable
        variables

{- | Add a new variable to the set of 'DeclaredVariables'.

The new variable must not already be declared.

 -}
newDeclaredVariable
    :: DeclaredVariables
    -> UnifiedVariable Variable
    -> PatternVerifier DeclaredVariables
newDeclaredVariable declared variable = do
    let declaredVariables = getDeclaredVariables declared
    case Map.lookup name declaredVariables of
        Just variable' -> alreadyDeclared variable'
        Nothing -> return (addDeclaredVariable variable declared)
  where
    name = foldMapVariable variableName variable
    alreadyDeclared
        :: UnifiedVariable Variable -> PatternVerifier DeclaredVariables
    alreadyDeclared variable' =
        koreFailWithLocations [variable', variable]
            (  "Variable '"
            <> getId name
            <> "' was already declared."
            )

{- | Collect 'DeclaredVariables'.

Each variable in the 'Foldable' collection must be unique.

See also: 'newDeclaredVariable'

 -}
uniqueDeclaredVariables
    :: Foldable f
    => f (UnifiedVariable Variable)
    -> PatternVerifier DeclaredVariables
uniqueDeclaredVariables =
    Foldable.foldlM newDeclaredVariable emptyDeclaredVariables

{- | Run a 'PatternVerifier' in a particular variable context.

See also: 'verifyStandalonePattern'

 -}
withDeclaredVariables
    :: DeclaredVariables
    -> PatternVerifier a
    -> PatternVerifier a
withDeclaredVariables declaredVariables' =
    Reader.local (\ctx -> ctx { declaredVariables = declaredVariables' })

applicationSortsFromSymbolOrAliasSentence
    :: SentenceSymbolOrAlias sentence
    => SymbolOrAlias
    -> sentence pat
    -> PatternVerifier ApplicationSorts
applicationSortsFromSymbolOrAliasSentence symbolOrAlias sentence = do
    Context { declaredSortVariables } <- Reader.ask
    mapM_
        (verifySort lookupSortDeclaration declaredSortVariables)
        (symbolOrAliasParams symbolOrAlias)
    symbolOrAliasSorts (symbolOrAliasParams symbolOrAlias) sentence

assertSameSort
    :: Sort
    -> Sort
    -> PatternVerifier ()
assertSameSort expectedSort actualSort =
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
    $ renderStrict . Pretty.layoutCompact
    $ "Expecting sort"
        <+> Pretty.squotes (unparse expectedSort)
        <+> "but got"
        <+> Pretty.squotes (unparse actualSort)
        <>  Pretty.dot

assertExpectedSort
    :: Maybe Sort
    -> Sort
    -> PatternVerifier ()
assertExpectedSort Nothing _ = return ()
assertExpectedSort (Just expected) actual =
    assertSameSort expected actual

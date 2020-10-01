{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Sentence
    ( Symbol (..)
    , groundSymbol
    , Alias (..)
    , SentenceAlias (..)
    , SentenceSymbol (..)
    , coerceSentenceSymbol
    , SentenceImport (..)
    , coerceSentenceImport
    , SentenceSort (..)
    , coerceSentenceSort
    , SentenceAxiom (..)
    , SentenceClaim (..)
    , sentenceClaimAttributes
    , SentenceHook (..)
    , coerceSentenceHook
    , Sentence (..)
    , projectSentenceImport
    , projectSentenceSort
    , projectSentenceSymbol
    , projectSentenceHookedSort
    , projectSentenceHookedSymbol
    , projectSentenceAlias
    , projectSentenceAxiom
    , projectSentenceClaim
    , sentenceAttributes
    , eraseSentenceAnnotations
    -- * Injections and projections
    , AsSentence (..)
    , SentenceSymbolOrAlias (..)
    -- * Type synonyms
    , PureSentenceSymbol
    , PureSentenceAlias
    , PureSentenceImport
    , PureSentenceAxiom
    , PureSentenceHook
    , PureSentence
    , PureModule
    , ParsedSentenceAlias
    , ParsedSentenceSymbol
    , ParsedSentenceImport
    , ParsedSentenceAxiom
    , ParsedSentenceSort
    , ParsedSentenceHook
    , ParsedSentence
    , ParsedModule
    -- * Re-exports
    , module Kore.Attribute.Attributes
    , module Kore.Syntax.Module
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Control.Monad as Monad
import Data.Coerce
import Data.Generics.Sum.Typed
    ( projectTyped
    )
import Data.Kind
    ( Type
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Attributes
import qualified Kore.Attribute.Null as Attribute
    ( Null (..)
    )
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    , freeVariable
    )
import Kore.Debug
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Module
import Kore.Syntax.Pattern
    ( Pattern
    )
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.Free
    ( freePureVariables
    )
import qualified Pretty

{- | @Symbol@ is the @head-constructor{sort-variable-list}@ part of the
@symbol-declaration@ syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).

See also: 'SymbolOrAlias'

 -}
data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![SortVariable]
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse Symbol where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor
        <> parameters symbolParams

    unparse2 Symbol { symbolConstructor } =
        unparse2 symbolConstructor


-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id -> Symbol
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

{- | 'Alias' corresponds to the @head-constructor{sort-variable-list}@ part of
the @alias-declaration@ and @alias-declaration@ syntactic categories from the
Semantics of K, Section 9.1.6 (Declaration and Definitions).

See also: 'SymbolOrAlias'.

 -}
data Alias = Alias
    { aliasConstructor :: !Id
    , aliasParams      :: ![SortVariable]
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse Alias where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor <> parameters aliasParams
    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

{- | 'SentenceAlias' corresponds to the @alias-declaration@ and syntactic
category from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

-}
data SentenceAlias (patternType :: Type) =
    SentenceAlias
        { sentenceAliasAlias        :: !Alias
        , sentenceAliasSorts        :: ![Sort]
        , sentenceAliasResultSort   :: !Sort
        , sentenceAliasLeftPattern
            :: !(Application SymbolOrAlias (SomeVariable VariableName))
        , sentenceAliasRightPattern :: !patternType
        , sentenceAliasAttributes   :: !Attributes
        }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse patternType => Unparse (SentenceAlias patternType) where
    unparse
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        Pretty.fillSep
            [ "alias"
            , unparse sentenceAliasAlias <> arguments sentenceAliasSorts
            , ":"
            , unparse sentenceAliasResultSort
            , "where"
            , unparse sentenceAliasLeftPattern
            , ":="
            , unparse sentenceAliasRightPattern
            , unparse sentenceAliasAttributes
            ]

    unparse2
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        Pretty.fillSep
            [ "alias"
            , unparse2 sentenceAliasAlias <> arguments2 sentenceAliasSorts
            , ":"
            , unparse2 sentenceAliasResultSort
            , "where"
            , unparse2 sentenceAliasLeftPattern
            , ":="
            , unparse2 sentenceAliasRightPattern
            , unparse2 sentenceAliasAttributes
            ]

{- | 'SentenceSymbol' is the @symbol-declaration@ and syntactic category from
the Semantics of K, Section 9.1.6 (Declaration and Definitions).

-}
data SentenceSymbol (patternType :: Type) =
    SentenceSymbol
        { sentenceSymbolSymbol     :: !Symbol
        , sentenceSymbolSorts      :: ![Sort]
        , sentenceSymbolResultSort :: !Sort
        , sentenceSymbolAttributes :: !Attributes
        }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse (SentenceSymbol patternType) where
    unparse
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
      =
        Pretty.fillSep
            [ "symbol"
            , unparse sentenceSymbolSymbol <> arguments sentenceSymbolSorts
            , ":"
            , unparse sentenceSymbolResultSort
            , unparse sentenceSymbolAttributes
            ]

    unparse2
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
      = Pretty.vsep
            [ Pretty.fillSep [ "symbol", unparse2 sentenceSymbolSymbol ]
            , Pretty.fillSep [ "axiom \\forall s Sorts"
                             , Pretty.parens (Pretty.fillSep
                                   [ "\\subset"
                                   , Pretty.parens (Pretty.fillSep
                                       [ unparse2 sentenceSymbolSymbol
                                       , unparse2Inhabitant sentenceSymbolSorts
                                       ])
                                   , unparse2 sentenceSymbolResultSort
                                   ])
                             ]
            ]
          where unparse2Inhabitant ss =
                  case ss of
                      [] -> ""
                      (s : rest) ->
                        Pretty.parens (Pretty.fillSep ["\\inh", unparse2 s])
                        <> unparse2Inhabitant rest

{- | Coerce the pattern type of a 'SentenceSymbol' to any other type.

This is trivial because the pattern type is a phantom parameter, that is,
'SentenceSymbol' does not contain any patterns.

See also: 'coerce'

 -}
coerceSentenceSymbol :: SentenceSymbol pattern1 -> SentenceSymbol pattern2
coerceSentenceSymbol = coerce

{- | 'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
-- TODO (thomas.tuegel): Even though the parameters are unused, they must stay
-- to satisfy the functional dependencies on 'AsSentence' below. Because they
-- are phantom, every use of 'asSentence' for a 'SentenceImport' will require a
-- type ascription. We should refactor the class so this is not necessary and
-- remove the parameters.
data SentenceImport (patternType :: Type) =
    SentenceImport
        { sentenceImportModuleName :: !ModuleName
        , sentenceImportAttributes :: !Attributes
        }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse (SentenceImport patternType) where
    unparse
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse sentenceImportModuleName
            , unparse sentenceImportAttributes
            ]

    unparse2
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse2 sentenceImportModuleName
            , unparse2 sentenceImportAttributes
            ]

{- | Coerce the pattern type of a 'SentenceImport' to any other type.

This is trivial because the pattern type is a phantom parameter, that is,
'SentenceImport' does not contain any patterns.

See also: 'coerce'

 -}
coerceSentenceImport :: SentenceImport pattern1 -> SentenceImport pattern2
coerceSentenceImport = coerce

{- | 'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceSort (patternType :: Type) =
    SentenceSort
        { sentenceSortName       :: !Id
        , sentenceSortParameters :: ![SortVariable]
        , sentenceSortAttributes :: !Attributes
        }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse (SentenceSort patternType) where
    unparse
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }
      =
        Pretty.fillSep
            [ "sort"
            , unparse sentenceSortName <> parameters sentenceSortParameters
            , unparse sentenceSortAttributes
            ]

    unparse2
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            }
      = Pretty.vsep
            [ Pretty.fillSep ["symbol", unparse2 sentenceSortName, "[sort]"]
            , Pretty.fillSep ["axiom"
                             , "\\subset"
                             , Pretty.parens (Pretty.fillSep
                                [ unparse2 sentenceSortName
                                , printLbSortsRb (length sentenceSortParameters)
                                ])
                             , "Sorts"
                             ]
            ]
      where printLbSortsRb n =
              case n of
                  0 -> ""
                  m -> Pretty.fillSep["(\\inh Sorts)", printLbSortsRb (m - 1)]

{- | Coerce the pattern type of a 'SentenceSort' to any other type.

This is trivial because the pattern type is a phantom parameter, that is,
'SentenceSort' does not contain any patterns.

See also: 'coerce'

 -}
coerceSentenceSort :: SentenceSort pattern1 -> SentenceSort pattern2
coerceSentenceSort = coerce

{- | 'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceAxiom (patternType :: Type) =
    SentenceAxiom
        { sentenceAxiomParameters :: ![SortVariable]
        , sentenceAxiomPattern    :: !patternType
        , sentenceAxiomAttributes :: !Attributes
        }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse patternType => Unparse (SentenceAxiom patternType) where
    unparse = unparseAxiom "axiom"
    unparse2 = unparseAxiom2 "axiom"

instance
    Ord variable
    => HasFreeVariables (SentenceAxiom (Pattern variable annotation)) variable
  where
    freeVariables =
        foldMap freeVariable
        . freePureVariables
        . sentenceAxiomPattern

unparseAxiom
    :: Unparse patternType
    => Pretty.Doc ann
    -> SentenceAxiom patternType
    -> Pretty.Doc ann
unparseAxiom
    label
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , parameters sentenceAxiomParameters
        , unparse sentenceAxiomPattern
        , unparse sentenceAxiomAttributes
        ]

unparseAxiom2
    :: Unparse patternType
    => Pretty.Doc ann
    -> SentenceAxiom patternType
    -> Pretty.Doc ann
unparseAxiom2
    label
    SentenceAxiom
        { sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , unparse2 sentenceAxiomPattern
        , unparse2 sentenceAxiomAttributes
        ]

{- | 'SentenceClaim' corresponds to the @claim-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
newtype SentenceClaim (patternType :: Type) =
    SentenceClaim { getSentenceClaim :: SentenceAxiom patternType }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

sentenceClaimAttributes :: SentenceClaim patternType -> Attributes
sentenceClaimAttributes = sentenceAxiomAttributes . getSentenceClaim

instance Unparse patternType => Unparse (SentenceClaim patternType) where
    unparse = unparseAxiom "claim" . getSentenceClaim
    unparse2 = unparseAxiom2 "claim" . getSentenceClaim

instance
    Ord variable
    => HasFreeVariables (SentenceClaim (Pattern variable annotation)) variable
  where
    freeVariables = freeVariables . getSentenceClaim


{- | @SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

See also: 'SentenceSort', 'SentenceSymbol'

 -}
data SentenceHook (patternType :: Type)
    = SentenceHookedSort !(SentenceSort patternType)
    | SentenceHookedSymbol !(SentenceSymbol patternType)
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse (SentenceHook patternType) where
    unparse =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse a
            SentenceHookedSymbol a -> "hooked-" <> unparse a

    unparse2 =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse2 a
            SentenceHookedSymbol a -> "hooked-" <> unparse2 a

{- | Coerce the pattern type of a 'SentenceHook' to any other type.

This is trivial because the pattern type is a phantom parameter, that is,
'SentenceHook' does not contain any patterns.

See also: 'coerce'

 -}
coerceSentenceHook :: SentenceHook pattern1 -> SentenceHook pattern2
coerceSentenceHook = coerce

{- | @Sentence@ is the @declaration@ syntactic category from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

-}
data Sentence (patternType :: Type)
    = SentenceAliasSentence  !(SentenceAlias patternType)
    | SentenceSymbolSentence !(SentenceSymbol patternType)
    | SentenceImportSentence !(SentenceImport patternType)
    | SentenceAxiomSentence  !(SentenceAxiom patternType)
    | SentenceClaimSentence  !(SentenceClaim patternType)
    | SentenceSortSentence   !(SentenceSort patternType)
    | SentenceHookSentence   !(SentenceHook patternType)
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse patternType => Unparse (Sentence patternType) where
     unparse = unparseGeneric
     unparse2 = unparse2Generic

projectSentenceImport
    :: Sentence ParsedPattern
    -> Maybe (SentenceImport ParsedPattern)
projectSentenceImport = projectTyped

projectSentenceSort
    :: Sentence ParsedPattern
    -> Maybe (SentenceSort ParsedPattern)
projectSentenceSort = projectTyped

projectSentenceSymbol
    :: Sentence ParsedPattern
    -> Maybe (SentenceSymbol ParsedPattern)
projectSentenceSymbol = projectTyped

projectSentenceHook
    :: Sentence ParsedPattern
    -> Maybe (SentenceHook ParsedPattern)
projectSentenceHook = projectTyped

projectSentenceHookedSort
    :: Sentence ParsedPattern
    -> Maybe (SentenceSort ParsedPattern)
projectSentenceHookedSort = projectSentenceHook Monad.>=> projectTyped

projectSentenceHookedSymbol
    :: Sentence ParsedPattern
    -> Maybe (SentenceSymbol ParsedPattern)
projectSentenceHookedSymbol = projectSentenceHook Monad.>=> projectTyped

projectSentenceAlias
    :: Sentence ParsedPattern
    -> Maybe (SentenceAlias ParsedPattern)
projectSentenceAlias = projectTyped

projectSentenceAxiom
    :: Sentence ParsedPattern
    -> Maybe (SentenceAxiom ParsedPattern)
projectSentenceAxiom = projectTyped

projectSentenceClaim
    :: Sentence ParsedPattern
    -> Maybe (SentenceClaim ParsedPattern)
projectSentenceClaim = projectTyped

{- | The attributes associated with a sentence.

Every sentence type has attributes, so this operation is total.

 -}
sentenceAttributes :: Sentence patternType -> Attributes
sentenceAttributes =
    \case
        SentenceAliasSentence
            SentenceAlias { sentenceAliasAttributes } ->
                sentenceAliasAttributes
        SentenceSymbolSentence
            SentenceSymbol { sentenceSymbolAttributes } ->
                sentenceSymbolAttributes
        SentenceImportSentence
            SentenceImport { sentenceImportAttributes } ->
                sentenceImportAttributes
        SentenceAxiomSentence
            SentenceAxiom { sentenceAxiomAttributes } ->
                sentenceAxiomAttributes
        SentenceClaimSentence
            (SentenceClaim SentenceAxiom { sentenceAxiomAttributes }) ->
                sentenceAxiomAttributes
        SentenceSortSentence
            SentenceSort { sentenceSortAttributes } ->
                sentenceSortAttributes
        SentenceHookSentence sentence ->
            case sentence of
                SentenceHookedSort
                    SentenceSort { sentenceSortAttributes } ->
                        sentenceSortAttributes
                SentenceHookedSymbol
                    SentenceSymbol { sentenceSymbolAttributes } ->
                        sentenceSymbolAttributes

-- | Erase the pattern annotations within a 'Sentence'.
eraseSentenceAnnotations
    :: Sentence (Pattern variable erased)
    -> Sentence (Pattern variable Attribute.Null)
eraseSentenceAnnotations sentence = (<$) Attribute.Null <$> sentence

class AsSentence sentenceType where
    asSentence :: sentenceType patternType -> Sentence patternType

instance AsSentence SentenceAlias where
    asSentence = SentenceAliasSentence

instance AsSentence SentenceSymbol where
    asSentence = SentenceSymbolSentence

instance AsSentence SentenceImport where
    asSentence = SentenceImportSentence

instance AsSentence SentenceAxiom where
    asSentence = SentenceAxiomSentence

instance AsSentence SentenceSort where
    asSentence = SentenceSortSentence

instance AsSentence SentenceHook where
    asSentence = SentenceHookSentence

class SentenceSymbolOrAlias (sentence :: Type -> Type) where
    getSentenceSymbolOrAliasConstructor
        :: sentence patternType -> Id
    getSentenceSymbolOrAliasSortParams
        :: sentence patternType -> [SortVariable]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence patternType -> [Sort]
    getSentenceSymbolOrAliasResultSort
        :: sentence patternType -> Sort
    getSentenceSymbolOrAliasAttributes
        :: sentence patternType -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence patternType -> String
    getSentenceSymbolOrAliasHead
        :: sentence patternType
        -> [Sort]
        -> SymbolOrAlias
    getSentenceSymbolOrAliasHead sentence sortParameters = SymbolOrAlias
        { symbolOrAliasConstructor =
            getSentenceSymbolOrAliasConstructor sentence
        , symbolOrAliasParams = sortParameters
        }

instance SentenceSymbolOrAlias SentenceAlias where
    getSentenceSymbolOrAliasConstructor = aliasConstructor . sentenceAliasAlias
    getSentenceSymbolOrAliasSortParams = aliasParams . sentenceAliasAlias
    getSentenceSymbolOrAliasArgumentSorts = sentenceAliasSorts
    getSentenceSymbolOrAliasResultSort = sentenceAliasResultSort
    getSentenceSymbolOrAliasAttributes = sentenceAliasAttributes
    getSentenceSymbolOrAliasSentenceName _ = "alias"

instance SentenceSymbolOrAlias SentenceSymbol where
    getSentenceSymbolOrAliasConstructor =
        symbolConstructor . sentenceSymbolSymbol
    getSentenceSymbolOrAliasSortParams = symbolParams . sentenceSymbolSymbol
    getSentenceSymbolOrAliasArgumentSorts = sentenceSymbolSorts
    getSentenceSymbolOrAliasResultSort = sentenceSymbolResultSort
    getSentenceSymbolOrAliasAttributes = sentenceSymbolAttributes
    getSentenceSymbolOrAliasSentenceName _ = "symbol"

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom = SentenceAxiom ParsedPattern

-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias = SentenceAlias ParsedPattern

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol = SentenceSymbol ParsedPattern

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport = SentenceImport ParsedPattern

-- | 'PureSentenceHook' is the pure (fixed-@level@) version of 'SentenceHook'.
type PureSentenceHook = SentenceHook ParsedPattern

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence = Sentence ParsedPattern

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule = Module PureSentence

type ParsedSentenceSort = SentenceSort ParsedPattern

type ParsedSentenceSymbol = SentenceSymbol ParsedPattern

type ParsedSentenceAlias = SentenceAlias ParsedPattern

type ParsedSentenceImport = SentenceImport ParsedPattern

type ParsedSentenceAxiom = SentenceAxiom ParsedPattern

type ParsedSentenceHook = SentenceHook ParsedPattern

type ParsedSentence = Sentence ParsedPattern

type ParsedModule = Module ParsedSentence

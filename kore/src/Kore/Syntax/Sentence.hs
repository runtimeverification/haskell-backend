{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Sentence
    ( Symbol (..)
    , groundSymbol
    , Alias (..)
    , ModuleName (..)
    , getModuleNameForError
    , SentenceAlias (..)
    , SentenceSymbol (..)
    , SentenceImport (..)
    , SentenceSort (..)
    , SentenceAxiom (..)
    , SentenceClaim (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
                 ( Hashable (..) )
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Attribute.Attributes
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Variable
import Kore.Unparser

{- | @Symbol@ is the @head-constructor{sort-variable-list}@ part of the
@symbol-declaration@ syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).

See also: 'SymbolOrAlias'

 -}
data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Symbol

instance NFData Symbol

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable Alias

instance NFData Alias

instance Unparse Alias where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor <> parameters aliasParams
    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

{- | 'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: Text }
    deriving (Eq, Generic, IsString, Ord, Show)

instance Hashable ModuleName

instance NFData ModuleName

instance Unparse ModuleName where
    unparse = Pretty.pretty . getModuleName
    unparse2 = Pretty.pretty . getModuleName


getModuleNameForError :: ModuleName -> String
getModuleNameForError = Text.unpack . getModuleName

{- | 'SentenceAlias' corresponds to the @alias-declaration@ and syntactic
category from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

-}
data SentenceAlias (patternType :: *) =
    SentenceAlias
        { sentenceAliasAlias        :: !Alias
        , sentenceAliasSorts        :: ![Sort]
        , sentenceAliasResultSort   :: !Sort
        , sentenceAliasLeftPattern  :: !(Application SymbolOrAlias Variable)
        , sentenceAliasRightPattern :: !patternType
        , sentenceAliasAttributes   :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceAlias patternType)

instance NFData patternType => NFData (SentenceAlias patternType)

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
data SentenceSymbol (patternType :: *) =
    SentenceSymbol
        { sentenceSymbolSymbol     :: !Symbol
        , sentenceSymbolSorts      :: ![Sort]
        , sentenceSymbolResultSort :: !Sort
        , sentenceSymbolAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSymbol patternType)

instance NFData (SentenceSymbol patternType)

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
                        (Pretty.parens (Pretty.fillSep ["\\inh", unparse2 s]))
                        <> (unparse2Inhabitant rest)

{- | 'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
-- TODO (thomas.tuegel): Even though the parameters are unused, they must stay
-- to satisfy the functional dependencies on 'AsSentence' below. Because they
-- are phantom, every use of 'asSentence' for a 'SentenceImport' will require a
-- type ascription. We should refactor the class so this is not necessary and
-- remove the parameters.
data SentenceImport (patternType :: *) =
    SentenceImport
        { sentenceImportModuleName :: !ModuleName
        , sentenceImportAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceImport patternType)

instance NFData (SentenceImport patternType)

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

{- | 'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceSort (patternType :: *) =
    SentenceSort
        { sentenceSortName       :: !Id
        , sentenceSortParameters :: ![SortVariable]
        , sentenceSortAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSort patternType)

instance NFData (SentenceSort patternType)

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

{- | 'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceAxiom (sortParam :: *) (patternType :: *) =
    SentenceAxiom
        { sentenceAxiomParameters :: ![sortParam]
        , sentenceAxiomPattern    :: !patternType
        , sentenceAxiomAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance
    (Hashable sortParam, Hashable patternType) =>
    Hashable (SentenceAxiom sortParam patternType)

instance
    (NFData sortParam, NFData patternType) =>
    NFData (SentenceAxiom sortParam patternType)

instance
    (Unparse sortParam, Unparse patternType) =>
    Unparse (SentenceAxiom sortParam patternType)
  where
    unparse = unparseAxiom "axiom"
    unparse2 = unparseAxiom2 "axiom"

unparseAxiom
    ::  ( Unparse patternType
        , Unparse sortParam
        )
    => Pretty.Doc ann
    -> SentenceAxiom sortParam patternType
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
    ::  ( Unparse patternType
        , Unparse sortParam
        )
    => Pretty.Doc ann
    -> SentenceAxiom sortParam patternType
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
newtype SentenceClaim (sortParam :: *) (patternType :: *) =
    SentenceClaim { getSentenceClaim :: SentenceAxiom sortParam patternType }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance
    (Hashable sortParam, Hashable patternType) =>
    Hashable (SentenceClaim sortParam patternType)

instance
    (NFData sortParam, NFData patternType) =>
    NFData (SentenceClaim sortParam patternType)

instance
    (Unparse sortParam, Unparse patternType) =>
    Unparse (SentenceClaim sortParam patternType)
  where
    unparse = unparseAxiom "claim" . getSentenceClaim
    unparse2 = unparseAxiom2 "claim" . getSentenceClaim

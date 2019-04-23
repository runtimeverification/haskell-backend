{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

module Kore.Implicit.ImplicitKore
    ( uncheckedKoreModule
    ) where

import           Data.Functor.Const
                 ( Const )
import qualified Data.Text as Text
import           Data.Void
                 ( Void )

import Kore.AST.Pure
import Kore.AST.Sentence

metaSortDescription
    :: MetaSortType -> Sentence Meta sortParam patternType
metaSortDescription sortType =
    SentenceSortSentence SentenceSort
        { sentenceSortName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
  where
    sentenceSortName = Id
        { getId = Text.pack (show sortType)
        , idLocation = AstLocationImplicit
        }

uncheckedKoreModule :: PureModule Meta (Const Void)
uncheckedKoreModule =
    Module
        { moduleName       = ModuleName "kore"
        , moduleSentences  = metaSortDescription <$> metaSortsList
        , moduleAttributes = Attributes []
        }

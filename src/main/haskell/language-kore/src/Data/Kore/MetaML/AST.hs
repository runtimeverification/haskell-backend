module Data.Kore.MetaML.AST where

import           Data.Fix

import           Data.Kore.AST

type MetaMLPattern var = Fix (Pattern Meta var)

data MetaSentenceAxiom = MetaSentenceAxiom
    { metaSentenceAxiomParameters :: ![SortVariable Meta]
    , metaSentenceAxiomPattern    :: !(MetaMLPattern Variable)
    , metaSentenceAxiomAttributes :: !Attributes
    }
    deriving (Eq, Show)

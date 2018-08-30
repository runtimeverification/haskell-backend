{-|

Module      : Kore.AST.Pretty
Description : Helpers for printing Kore AST
Copyright   : 2018 Runtime Verification, Inc.
License     : NCSA
Stability   : experimental

 -}

module Kore.AST.Pretty
    ( module Data.Text.Prettyprint.Doc
    , arguments, arguments', noArguments
    , attributes, attributes'
    , parameters
    , fromString
    , layoutPrettyUnbounded
    ) where

import Data.String
       ( fromString )
import Data.Text.Prettyprint.Doc hiding
       ( list )

-- TODO: Refer to semantics document for syntactic rules.


-- | Print a list of sort parameters.
parameters :: Pretty a => [a] -> Doc ann
parameters = parameters' . map pretty

-- | Print a list of documents as sort parameters.
parameters' :: [Doc ann] -> Doc ann
parameters' = list lbrace rbrace

-- | Print a list of documents as arguments.
arguments' :: [Doc ann] -> Doc ann
arguments' = list lparen rparen

-- | Print a list of arguments.
arguments :: Pretty a => [a] -> Doc ann
arguments = arguments' . map pretty

-- | Print a list of no arguments.
noArguments :: Doc ann
noArguments = arguments' []

-- | Print a list of documents as attributes.
attributes' :: [Doc ann] -> Doc ann
attributes' = list lbracket rbracket

-- | Print a list of attributes.
attributes :: Pretty a => [a] -> Doc ann
attributes = attributes' . map pretty

-- | Print a list of documents separated by commas in the preferred Kore format.
list
    :: Doc ann  -- ^ opening list delimiter
    -> Doc ann  -- ^ closing list delimiter
    -> [Doc ann]  -- ^ list items
    -> Doc ann
list left right =
    \case
        [] -> left <> right
        xs -> (group . (<> close) . nest 4 . (open <>) . vsep . punctuate between) xs
  where
    open = left <> line'
    close = line' <> right
    between = comma

-- | Render a 'Doc ann' with indentation and without extra line breaks.
layoutPrettyUnbounded :: Doc ann -> SimpleDocStream ann
layoutPrettyUnbounded = layoutPretty LayoutOptions { layoutPageWidth = Unbounded }

module Kore.Attribute.Parser
    ( Parser
    , ParseError
    , ParseAttributes (..)
    ) where

import Data.Default
       ( Default )

import Kore.AST.Sentence
       ( Attributes )
import Kore.Error
       ( Error )

data ParseError

type Parser = Either (Error ParseError)

class Default atts => ParseAttributes atts where
    {- | Parse 'Attributes'

      The parser may signal failure using 'throwError' and recover with
      'catchError'. The caller runs the parser with 'runExcept'.
     -}
    parseAttributes :: Attributes -> Parser atts

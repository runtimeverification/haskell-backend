{-|
Module      : Data.Attribute.Subsort
Description : Representation and parser for subsort attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Attribute.Subsort where

import Data.Hashable
    ( Hashable
    )

import Kore.Attribute.Parser as Parser

{- | The @subsort@ attribute. -}
data Subsort = Subsort
    { subsort :: Sort
    , supersort :: Sort
    }
    deriving (Eq, Generic, Ord, Show)

instance Hashable Subsort

newtype Subsorts = Subsorts { getSubsorts :: [Subsort] }
    deriving (Eq, Ord, Show)

instance Default Subsorts where
    def = Subsorts []

-- | Kore identifier representing a @subsort@ attribute symbol.
subsortId :: Id
subsortId = "subsort"

{- | Kore symbol representing a @subsort@ attribute head.

Kore syntax: @subsort{Sub,Super}@
where @Sub@ is the subsort and @Super@ is the supersort.

 -}
subsortSymbol :: Sort -> Sort -> SymbolOrAlias
subsortSymbol subsort supersort =
    SymbolOrAlias
        { symbolOrAliasConstructor = subsortId
        , symbolOrAliasParams = [ subsort, supersort ]
        }

{- | Kore pattern representing a @subsort@ attribute.

Kore syntax: @subsort{Sub,Super}()@
where @Sub@ is the subsort and @Super@ is the supersort.

 -}
subsortAttribute :: Sort -> Sort -> AttributePattern
subsortAttribute subsort supersort =
    attributePattern_ $ subsortSymbol subsort supersort

{- | Parse @subsort@ Kore attributes, if present.

  It is a parse error if the @subsort@ attribute is not given exactly
  two sort parameters

  See also: 'subsortAttribute'

 -}
instance ParseAttributes Subsorts where
    parseAttribute =
        withApplication' $ \params args (Subsorts subsorts) -> do
            Parser.getZeroArguments args
            (subsort, supersort) <- Parser.getTwoParams params
            let relation = Subsort subsort supersort
            return (Subsorts $ relation : subsorts)
      where
        withApplication' = Parser.withApplication subsortId

    toAttributes =
        Attributes . map toAttribute . getSubsorts
      where
        toAttribute = subsortAttribute <$> subsort <*> supersort

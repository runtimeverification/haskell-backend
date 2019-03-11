{-|
Module      : Control.Lens.TH.Rules
Description : Alternate lens rules
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

'verboseLensRules' is an alternate set of lens rules which generates
verbosely-named field lenses to avoid colliding with the record selectors, which
may still be used.

-}
module Control.Lens.TH.Rules
    ( verboseLensRules
    , makeLenses
    ) where

import           Control.Lens
                 ( (&) )
import qualified Control.Lens as Lens
import           Control.Lens.TH
                 ( LensRules )
import qualified Data.Char as Char
import           Language.Haskell.TH
                 ( DecsQ, Name )

{- | Rules to make field lenses prefixed by "lens".

A field named @≪foo≫@ will have a lens named @≪lensFoo≫@, to avoid colliding
with the record selector.

 -}
verboseLensRules :: LensRules
verboseLensRules =
    Lens.lensRules
    & Lens.set Lens.lensField fieldNamer
  where
    fieldNamer =
        Lens.mappingNamer fieldNamerWorker
      where
        fieldNamerWorker [] = []
        fieldNamerWorker (n : ame) =
            ["lens" ++ Char.toUpper n : ame]

makeLenses :: Name -> DecsQ
makeLenses = Lens.makeLensesWith verboseLensRules

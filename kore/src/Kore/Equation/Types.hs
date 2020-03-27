{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Types
    ( Equation (..)
    , mkEquation
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Default as Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( TermLike
    , termLikeSort
    )
import Kore.Internal.Variable
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

data Equation variable = Equation
    { requires :: !(Predicate variable)
    , left  :: !(TermLike variable)
    , right :: !(TermLike variable)
    , ensures :: !(Predicate variable)
    , attributes :: !(Attribute.Axiom Symbol variable)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance NFData variable => NFData (Equation variable)

instance SOP.Generic (Equation variable)

instance SOP.HasDatatypeInfo (Equation variable)

instance Debug variable => Debug (Equation variable)

instance (Debug variable, Diff variable) => Diff (Equation variable)

instance InternalVariable variable => Pretty (Equation variable) where
    pretty equation@(Equation _ _ _ _ _) =
        Pretty.vsep
            [ "requires:"
            , Pretty.indent 4 (unparse requires)
            , "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        Equation
            { requires
            , left
            , right
            , ensures
            } = equation

instance TopBottom (Equation variable) where
    isTop _ = False
    isBottom _ = False

instance SQL.Table (Equation Variable)

instance SQL.Column (Equation Variable) where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

-- | Creates a basic, unconstrained, Equality pattern
mkEquation
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Equation variable
mkEquation left right =
    assert (termLikeSort left == termLikeSort right)
    Equation
        { left
        , requires = Predicate.makeTruePredicate sort
        , right
        , ensures = Predicate.makeTruePredicate sort
        , attributes = Default.def
        }
  where
    sort = termLikeSort left

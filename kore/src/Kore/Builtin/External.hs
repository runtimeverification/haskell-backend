{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Builtin.External
    ( externalize
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Functor.Foldable as Recursive
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin.Bool.Bool as Bool
import qualified Kore.Builtin.Int.Int as Int
import qualified Kore.Builtin.List.List as List
import qualified Kore.Builtin.Map.Map as Map
import qualified Kore.Builtin.Set.Set as Set
import qualified Kore.Builtin.String.String as String
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Internal.Alias as Alias
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import qualified Kore.Syntax.Pattern as Syntax

{- | Externalize the 'TermLike' into a 'Syntax.Pattern'.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'

 -}
externalize
    ::  forall variable
    .   InternalVariable variable
    =>  TermLike variable
    ->  Syntax.Pattern variable Attribute.Null
externalize =
    Recursive.unfold worker
  where
    worker
        ::  TermLike variable
        ->  Recursive.Base
                (Syntax.Pattern variable Attribute.Null)
                (TermLike variable)
    worker termLike =
        case termLikeF of
            BuiltinF domain ->
                case domain of
                    Domain.BuiltinMap  builtin ->
                        (toPatternF . Recursive.project)
                            (Map.asTermLike builtin)
                    Domain.BuiltinList builtin ->
                        (toPatternF . Recursive.project)
                            (List.asTermLike builtin)
                    Domain.BuiltinSet  builtin ->
                        (toPatternF . Recursive.project)
                            (Set.asTermLike builtin)
                    Domain.BuiltinInt  builtin ->
                        (toPatternF . Recursive.project)
                            (Int.asTermLike builtin)
                    Domain.BuiltinBool builtin ->
                        (toPatternF . Recursive.project)
                            (Bool.asTermLike builtin)
                    Domain.BuiltinString builtin ->
                        (toPatternF . Recursive.project)
                            (String.asTermLike builtin)
            _ -> toPatternF termLikeBase
      where
        termLikeBase@(_ :< termLikeF) = Recursive.project termLike

    toPatternF
        :: GHC.HasCallStack
        => Recursive.Base (TermLike variable) (TermLike variable)
        -> Recursive.Base
            (Syntax.Pattern variable Attribute.Null)
            (TermLike variable)
    toPatternF (_ :< termLikeF) =
        (Attribute.Null :<)
        $ case termLikeF of
            AndF andF -> Syntax.AndF andF
            ApplyAliasF applyAliasF ->
                Syntax.ApplicationF
                $ mapHead Alias.toSymbolOrAlias applyAliasF
            ApplySymbolF applySymbolF ->
                Syntax.ApplicationF
                $ mapHead Symbol.toSymbolOrAlias applySymbolF
            BottomF bottomF -> Syntax.BottomF bottomF
            CeilF ceilF -> Syntax.CeilF ceilF
            DomainValueF domainValueF -> Syntax.DomainValueF domainValueF
            EqualsF equalsF -> Syntax.EqualsF equalsF
            ExistsF existsF -> Syntax.ExistsF existsF
            FloorF floorF -> Syntax.FloorF floorF
            ForallF forallF -> Syntax.ForallF forallF
            IffF iffF -> Syntax.IffF iffF
            ImpliesF impliesF -> Syntax.ImpliesF impliesF
            InF inF -> Syntax.InF inF
            MuF muF -> Syntax.MuF muF
            NextF nextF -> Syntax.NextF nextF
            NotF notF -> Syntax.NotF notF
            NuF nuF -> Syntax.NuF nuF
            OrF orF -> Syntax.OrF orF
            RewritesF rewritesF -> Syntax.RewritesF rewritesF
            StringLiteralF stringLiteralF ->
                Syntax.StringLiteralF stringLiteralF
            TopF topF -> Syntax.TopF topF
            VariableF variableF -> Syntax.VariableF variableF
            InhabitantF inhabitantF -> Syntax.InhabitantF inhabitantF
            EvaluatedF evaluatedF ->
                Cofree.tailF
                $ worker
                $ getEvaluated evaluatedF
            BuiltinF _ -> error "Unexpected internal builtin"

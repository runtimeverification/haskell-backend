{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.External (
    externalize,
) where

import Control.Monad.Free (Free (..))
import Data.Functor.Const (
    Const (..),
 )
import qualified Data.Functor.Foldable as Recursive
import qualified Kore.Attribute.Null as Attribute
import Kore.Attribute.Synthetic (
    synthesize,
 )
import qualified Kore.Builtin.Bool.Bool as Bool
import qualified Kore.Builtin.Endianness.Endianness as Endianness
import qualified Kore.Builtin.Int.Int as Int
import qualified Kore.Builtin.InternalBytes.InternalBytes as InternalBytes
import qualified Kore.Builtin.List.List as List
import qualified Kore.Builtin.Map.Map as Map
import qualified Kore.Builtin.Set.Set as Set
import qualified Kore.Builtin.Signedness.Signedness as Signedness
import qualified Kore.Builtin.String.String as String
import qualified Kore.Internal.Alias as Alias
import qualified Kore.Internal.Inj as Inj
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import qualified Kore.Syntax.Pattern as Syntax
import Prelude.Kore

type Futu t a =
    a -> Recursive.Base t (Free (Recursive.Base t) a)

{- | Externalize the 'TermLike' into a 'Syntax.Pattern'.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'
-}
externalize ::
    forall variable.
    InternalVariable variable =>
    TermLike variable ->
    Syntax.Pattern variable Attribute.Null
externalize =
    Recursive.futu externalize1
  where
    externalize1 ::
        Futu (Syntax.Pattern variable Attribute.Null) (TermLike variable)
    externalize1 termLike =
        -- TODO (thomas.tuegel): Make all these cases into classes.
        case termLikeF of
            AndF andF                 -> (Attribute.Null :<) $ Syntax.AndF         $ fmap Pure andF
            ApplyAliasF applyAliasF   -> mkApp $ mapHead Alias.toSymbolOrAlias applyAliasF
            ApplySymbolF applySymbolF -> mkApp $ mapHead Symbol.toSymbolOrAlias applySymbolF
            BottomF bottomF           -> (Attribute.Null :<) $ Syntax.BottomF      $ fmap Pure bottomF
            CeilF   ceilF             -> (Attribute.Null :<) $ Syntax.CeilF        $ fmap Pure ceilF
            DomainValueF domainValueF -> (Attribute.Null :<) $ Syntax.DomainValueF $ fmap Pure domainValueF
            EqualsF equalsF           -> (Attribute.Null :<) $ Syntax.EqualsF      $ fmap Pure equalsF
            ExistsF existsF           -> (Attribute.Null :<) $ Syntax.ExistsF      $ fmap Pure existsF
            FloorF floorF             -> (Attribute.Null :<) $ Syntax.FloorF       $ fmap Pure floorF
            ForallF forallF           -> (Attribute.Null :<) $ Syntax.ForallF      $ fmap Pure forallF
            IffF iffF                 -> (Attribute.Null :<) $ Syntax.IffF         $ fmap Pure iffF
            ImpliesF impliesF         -> (Attribute.Null :<) $ Syntax.ImpliesF     $ fmap Pure impliesF
            InF inF                   -> (Attribute.Null :<) $ Syntax.InF          $ fmap Pure inF
            MuF muF                   -> (Attribute.Null :<) $ Syntax.MuF          $ fmap Pure muF
            NextF nextF               -> (Attribute.Null :<) $ Syntax.NextF        $ fmap Pure nextF
            NotF notF                 -> (Attribute.Null :<) $ Syntax.NotF         $ fmap Pure notF
            NuF nuF                   -> (Attribute.Null :<) $ Syntax.NuF          $ fmap Pure nuF
            OrF orF                   -> (Attribute.Null :<) $ Syntax.OrF          $ fmap Pure orF
            RewritesF rewritesF       -> (Attribute.Null :<) $ Syntax.RewritesF    $ fmap Pure rewritesF
            StringLiteralF stringLiteralF -> (Attribute.Null :<) $
                Syntax.StringLiteralF $ fmap Pure stringLiteralF
            TopF topF                 -> (Attribute.Null :<) $ Syntax.TopF         $ fmap Pure topF
            VariableF variableF       -> (Attribute.Null :<) $ Syntax.VariableF    $ fmap Pure variableF
            InhabitantF inhabitantF   -> (Attribute.Null :<) $ Syntax.InhabitantF  $ fmap Pure inhabitantF
            EndiannessF endiannessF   -> mkApp $ mapHead Symbol.toSymbolOrAlias $
                Endianness.toApplication $ getConst endiannessF
            SignednessF signednessF   -> mkApp $ mapHead Symbol.toSymbolOrAlias $
                Signedness.toApplication $ getConst signednessF
            -- Internals
            InternalBoolF (Const internalBool) -> Bool.externalize1 internalBool
            InternalIntF (Const internalInt) -> Int.externalize1 internalInt
            InternalBytesF (Const internalBytes) -> InternalBytes.externalize1 internalBytes
            InternalStringF (Const internalString) -> String.externalize1 internalString
            InjF inj -> mkApp $ mapHead Symbol.toSymbolOrAlias (Inj.toApplication inj)
            InternalListF internalList -> List.externalize1 internalList
            InternalSetF internalSet -> either externalize1 id $ Set.externalize1 internalSet
            InternalMapF internalMap -> either externalize1 id $ Map.externalize1 internalMap
      where
        _ :< termLikeF = Recursive.project termLike
        mkApp = (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
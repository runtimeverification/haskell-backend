{-|
Module      : Kore.ASTUtils.Substitution
Description : Substitute phi_1 for phi_2, avoiding capture
              In particular this implements axiom 7 in
              the "large" axiom set (Rosu 2017).
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Kore.ASTUtils.Substitution
    ( subst
    ) where

import           Data.Functor.Classes
                 ( Eq1 )
import           Data.Functor.Foldable
import qualified Data.Set as S
import qualified Data.Text as Text

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Variables.Free

-- | subst phi_1 phi_2 phi = phi[phi_2/phi_1]
-- Note that different papers use different conventions.
-- Here `phi_1` is the old pattern that disappears
-- and `phi_2` is the new pattern that replaces it.
subst
    ::  ( Eq1 domain, Traversable domain
        , MetaOrObject level
        )
    => PurePattern level domain Variable (Valid level)
    -> PurePattern level domain Variable (Valid level)
    -> PurePattern level domain Variable (Valid level)
    -> PurePattern level domain Variable (Valid level)
subst old new =
    \case
        Forall_ _ v p -> handleBinder old new mkForall v p
        Exists_ _ v p -> handleBinder old new mkExists v p
        pat
          | pat == old -> new
          | otherwise  -> embed $ fmap (subst old new) $ project pat

handleBinder
    ::  ( Eq1 domain, Traversable domain
        , MetaOrObject level
        , pattern' ~ PurePattern level domain Variable (Valid level)
        )
    => pattern'
    -> pattern'
    -> (Variable level -> pattern' -> pattern')
    -- ^ Binder constructor
    -> Variable level
    -> pattern'
    -> pattern'
handleBinder old new mkBinder v p
  | S.member v (freePureVariables old) = mkBinder v p
  | S.member v (freePureVariables new) = subst old new renamed
  | otherwise = mkBinder v $ subst old new p
  where
    renamed = mkBinder v' (subst (mkVar v) (mkVar v') p)
    v' = head $ filter (not . flip S.member freeVarsP) $ alternatives v
    freeVarsP = freePureVariables p
    alternatives (Variable (Id name loc) sort) =
        [ Variable (Id (name <> (Text.pack . show) n) loc) sort
        | n <- [(0::Integer)..]
        ]

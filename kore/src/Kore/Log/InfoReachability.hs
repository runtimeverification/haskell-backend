{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.InfoReachability (
    InfoReachability (..),
    whileReachability,
) where

import Kore.Reachability.Prim
import Log
import Prelude.Kore
import Pretty (
    Doc,
    Pretty,
    (<+>),
 )
import qualified Pretty

newtype InfoReachability = InfoReachability {prim :: Prim}
    deriving (Show)

instance Pretty InfoReachability where
    pretty InfoReachability{prim} =
        (Pretty.hsep . catMaybes) [primDoc prim]

instance Entry InfoReachability where
    entrySeverity _ = Info
    shortDoc InfoReachability{prim} = (<+>) "while" <$> primDoc prim
    helpDoc _ = "log reachability proof steps"

primDoc :: Prim -> Maybe (Doc ann)
primDoc Simplify = Just "simplifying the claim"
primDoc CheckImplication = Just "checking the implication"
primDoc ApplyClaims = Just "applying claims"
primDoc ApplyAxioms = Just "applying axioms"
primDoc _ = Nothing

whileReachability ::
    MonadLog log =>
    Prim ->
    log a ->
    log a
whileReachability prim
    | Just _ <- primDoc prim = logWhile InfoReachability{prim}
    | otherwise = id

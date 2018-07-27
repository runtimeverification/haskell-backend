{-|
Module      : Kore.Proof.LineBasedProof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

-- DO NOT REVIEW THIS FILE
-- It works for now, but is extremely ugly and brittle.
-- I mostly wrote it to get good pretty print output.
-- A more sophisticated hash consing system will come when needed.

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# OPTIONS_GHC -Wno-unused-matches    #-}
{-# OPTIONS_GHC -Wno-name-shadowing    #-}


module Kore.Proof.LineBasedProof
( toLineProof
, printLineProof
)
where

import Control.Lens
import Control.Monad.State.Strict

import           Data.Functor.Foldable
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Data.Hashable
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Util
import Kore.Proof.Proof

data LineBasedProof = LineBasedProof
    { unLineBasedProof :: M.Map Int (PropF Term LargeRule Int Int)}

toLineProof :: Proof -> LineBasedProof
toLineProof proof =
    LineBasedProof $ execState (go proof) (M.empty, M.empty, M.empty, 1) ^. _3
    where
        go (Fix proof) = do
            j' <- mapM go $ justification proof
            a' <- S.fromList <$>
                (mapM lookupAssumptions $ S.toList $ assumptions proof)
            let proof' = proof { justification = j' , assumptions = a' }
            let h = hash proof'
            (!assumptionsTable, !hashTable, !orderedTable, !next) <- get
            case M.lookup h hashTable of
              Just m -> do
                return m
              Nothing -> do
                put ( if isAssumption j'
                          then
                              M.insert
                              (hash $ conclusion proof')
                              next
                              assumptionsTable
                          else assumptionsTable
                    , M.insert h next hashTable
                    , M.insert next proof' orderedTable
                    , next+1)
                return next
        lookupAssumptions assumption = do
            let h = hash assumption
            (!assumptionsTable, !hashTable, !orderedTable, !next) <- get
            case M.lookup h assumptionsTable of
                Nothing -> return next
                Just m  -> return m

isAssumption :: LargeRule subproof -> Bool
isAssumption = \case
    Assumption _ -> True
    _ -> False

instance Pretty LineBasedProof where
    pretty proof = (vsep
      $ map (\(n, ByF claim justification assumptions) ->
          fill 60 (
             fill 3 (pretty n)
             <> " : "
             <> encloseSep mempty mempty "," (map pretty $ S.toList assumptions)
             <> " |- "
             <> align (pretty claim)
             <> space
           )
           <> line
           <> indent 10 ("By " <> pretty justification)
        )
      $ M.toList
      $ unLineBasedProof proof) <> line

printLineProof :: Proof -> IO ()
printLineProof = putDocW 100 . pretty . toLineProof









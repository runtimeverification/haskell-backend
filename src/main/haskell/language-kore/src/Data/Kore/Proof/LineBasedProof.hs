{-|
Module      : Data.Kore.Proof.LineBasedProof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

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



module Data.Kore.Proof.LineBasedProof where

import           Control.Arrow
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State.Strict

import           Data.List
import           Data.Fix
import           Data.Foldable
import           Data.Kore.AST.Common hiding (line)
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools
import qualified Data.Map.Strict                       as M
import           Data.Maybe
import           Data.Reflection
import qualified Data.Set                              as S


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Coerce
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Util


import           Data.Functor.Compose
import           Data.Hashable
import           GHC.Generics                          (Generic)
import           Unsafe.Coerce

data LineBasedProof = LineBasedProof
    { unLineBasedProof :: M.Map Int (PropF Term (LargeRule Int) Int Int)}

assumptionsLens f (Discharge a b) = Discharge <$> (f a) <*> pure b
assumptionsLens f a = pure a 

toLineProof :: Proof -> LineBasedProof
toLineProof proof =
    LineBasedProof $ execState (go proof) (M.empty, M.empty, 1) ^. _2
    where 
        go :: Proof -> State (M.Map Int Int, M.Map Int (PropF Term (LargeRule Int) Int Int), Int) Int 
        go (Fix proof) = do 
            j' <- mapM go $ justification proof
            j'' <- traverseOf assumptionsLens (unsafeCoerce lookupAssumptions) $ unsafeCoerce j'
            a' <- S.fromList <$> (mapM lookupAssumptions $ S.toList $ assumptions proof)
            let proof' = proof { justification = unsafeCoerce j' , assumptions = a' }
            let h = hash proof'
            (!hashTable, !orderedTable, !next) <- get 
            case M.lookup h hashTable of 
              Just m -> do 
                return m 
              Nothing -> do 
                put ( M.insert h next hashTable
                    , M.insert next proof' orderedTable
                    , next+1)
                return next
        lookupAssumptions :: Term -> State (M.Map Int Int, M.Map Int (PropF Term (LargeRule Int) Int Int), Int) Int 
        lookupAssumptions assumption = do 
            let line = ByF assumption (Assumption assumption) (S.singleton (0::Int)) :: PropF Term (LargeRule Int) Int Int 
            let h = hash line 
            (!hashTable, !orderedTable, !next) <- get 
            case M.lookup h hashTable of 
                Nothing -> return 0
                Just m -> return m 

-- instance Pretty LineBasedProof where 
--     pretty m = go $ M.toList $ unLineBasedProof m
--         where go ((n, s) : xs) = pretty n <> " : " <> pretty s <> line <> go xs
--               go [] = mempty

testProof = dummyEnvironment $ useRule $ AndIntro (useRule TopIntro) (useRule $ Assumption mkBottom)

instance Pretty LineBasedProof where 
    pretty proof = (vsep
      $ map (\(n, ByF claim justification assumptions) -> 
        fillBreak 80 (
         fillBreak 3 (pretty n)
         <> " : " 
         <> " |- " 
         <> pretty claim)
         <> pretty justification 
         <> line 
         <> indent 10 (
            pretty $ S.toList assumptions
            )
         ) 
      $ M.toList 
      $ unLineBasedProof proof) <> line 

printLineProof = putDocW 100 . pretty . toLineProof

-- instance Pretty LineBasedProof where 
--     pretty m = vsep [lineNumbers, statements, justifications]
--         where lineNumbers = vsep $ map (pretty . fst) m'
--                   -- foldl1 (<>) $ 
--                   -- intercalate 
--                   --     (repeat line) 
--                   --     (map (\x -> [pretty x]) [1..(length m')]) 
--               statements = vsep $ map (pretty . conclusion . snd) m'
--               justifications = vsep $ map (pretty . justification . snd) m'
--               m' = M.toList $ unLineBasedProof m 



-- getIdx 
--     :: (MonadState s m, Hashable a) 
--     => a 
--     -> Lens' s (M.Map Int Int)
--     -> Lens' s Int
--     -> m Int 
-- getIdx q storeLens nextLens = do 
--     let h = hash q 
--     store <- use storeLens
--     next <- use nextLens
--     case M.lookup h store of 
--         Nothing -> do 
--             storeLens %= M.insert h next
--             nextLens %= (1+)
--             return next
--         Just m -> return m


-- toLineProof :: Proof -> LineBasedProof
-- toLineProof proof =
--     execState (go proof) (M.empty, M.empty, M.empty, 0) ^. _2
--     where 
--         go :: Proof -> State (M.Map Int Int, LineBasedProof, M.Map Int Int, Int) Int 
--         go (Fix proof) = do 
--             a' <- S.fromList <$> (mapM goAssumption $ S.toList $ assumptions proof)
--             j' <- mapM go $ justification proof
--             let proof' = proof { justification = j', assumptions = a' }
--             let h = hash proof'
--             ( !hashTable, !orderedTable, !assumptionsTable, !next) <- get 
--             case M.lookup h hashTable of 
--               Just m -> do 
--                 return m 
--               Nothing -> do 
--                 put ( M.insert h next hashTable
--                     , M.insert next proof' orderedTable
--                     , assumptionsTable
--                     , next+1)
--                 return next
--         goAssumption (Fix assumption) = do 
--             (!hashTable, !orderedTable, !assumptionsTable, !next) <- get 
--             let h = hash assumption
--             case M.lookup h assumptionsTable of 
--                 Nothing -> do 
--                     put (hashTable, orderedTable, M.insert h next assumptionsTable, next + 1)
--                     return next 
--                 Just m -> do 
--                     return m 

-- toLineProof :: Proof -> LineBasedProof
-- toLineProof proof =
--     execState (go proof) (M.empty, M.empty, M.empty, 0) ^. _2
--     where 
--         go :: Proof -> State (M.Map Int Int, LineBasedProof, M.Map Int Int, Int) Int 
--         go (Fix proof) = do 
--             j' <- mapM go $ justification proof
--             a' <- S.fromList <$> (mapM goAssumption $ S.toList $ assumptions proof)
--             let proof' = proof { justification = j', assumptions = a' }
--             let h = hash proof'
--             ( !hashTable, !orderedTable, !assumptionsTable, !next) <- get 
--             case M.lookup h hashTable of 
--               Just m -> do 
--                 return m 
--               Nothing -> do 
--                 put ( M.insert h next hashTable
--                     , M.insert next proof' orderedTable
--                     , assumptionsTable
--                     , next+1)
--                 return next
--         goAssumption assumption = undefined







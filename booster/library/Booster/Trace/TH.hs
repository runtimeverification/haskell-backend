{-# HLINT ignore "Use typeRep" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Booster.Trace.TH (mkSumPatterns) where

import Data.Data (Typeable)
import Data.Kind (Type)
import Data.Typeable (typeOf)
import Language.Haskell.TH qualified as TH

mkEitherType :: Int -> TH.Q TH.Type
mkEitherType pos = do
    a <- TH.newName "a"
    eithr <- go pos a
    pure $ TH.AppT (TH.AppT TH.ArrowT $ TH.VarT a) eithr
  where
    go :: Int -> TH.Name -> TH.Q TH.Type
    go p a
        | p <= 0 = do
            b <- TH.newName "b"
            pure $ TH.AppT (TH.AppT (TH.ConT ''Either) (TH.VarT a)) (TH.VarT b)
        | otherwise = do
            b <- TH.newName "b"
            rest <- go (p - 1) a
            pure $ TH.AppT (TH.AppT (TH.ConT ''Either) (TH.VarT b)) rest

mkUnmatchedType :: Int -> TH.Q TH.Type
mkUnmatchedType pos
    | pos <= 0 = do
        b <- TH.newName "b"
        pure $ TH.AppT (TH.AppT (TH.ConT ''Either) (TH.VarT b)) $ TH.ConT ''()
    | otherwise = do
        b <- TH.newName "b"
        rest <- mkUnmatchedType (pos - 1)
        pure $ TH.AppT (TH.AppT (TH.ConT ''Either) (TH.VarT b)) rest

mkEitherPat :: TH.Name -> Int -> TH.Pat
mkEitherPat x pos
    | pos <= 0 = TH.ConP 'Left [] [TH.VarP x]
    | otherwise = TH.ConP 'Right [] [mkEitherPat x $ pos - 1]

mkUnmatchedPat :: Int -> TH.Pat
mkUnmatchedPat pos
    | pos <= 0 = TH.ConP 'Right [] [TH.ConP '() [] []]
    | otherwise = TH.ConP 'Right [] [mkUnmatchedPat $ pos - 1]

mkPattern :: TH.Name -> Int -> TH.Q [TH.Dec]
mkPattern name pos = do
    x <- TH.newName "x"
    ty <- mkEitherType pos

    pure
        [ -- pattern <name> :: a -> ... Either a ...
          TH.PatSynSigD name ty
        , -- pattern <name> x = Right (... Left x ...)
          TH.PatSynD
            name
            (TH.PrefixPatSyn [x])
            TH.ImplBidir
            $ mkEitherPat x pos
        ]

mkUnmatchedPattern :: Int -> [TH.Name] -> TH.Q [TH.Dec]
mkUnmatchedPattern pos names = do
    let name = TH.mkName "Unmatched"
    ty <- mkUnmatchedType pos

    pure
        [ -- pattern Unmatched :: Either (... Either a () ...)
          TH.PatSynSigD name ty
        , -- pattern Unmatched = Right (... Right () ...)
          TH.PatSynD
            name
            (TH.PrefixPatSyn [])
            TH.ImplBidir
            $ mkUnmatchedPat pos
        , -- {-# COMPLETE C_1E, ..., C_iE, Unmatched #-}
          TH.PragmaD $ TH.CompleteP (names ++ [name]) Nothing
        ]

class MkSumPatterns (es :: [Type]) where
    mkSumPatterns' :: proxy es -> Int -> [TH.Name] -> TH.Q [TH.Dec]

instance MkSumPatterns '[] where
    mkSumPatterns' _ pos = mkUnmatchedPattern (pos - 1)

instance (Typeable e, MkSumPatterns es) => MkSumPatterns (e ': es) where
    mkSumPatterns' _ pos names = do
        let name = TH.mkName $ (show $ typeOf (undefined :: e)) ++ "E"
        (++) <$> mkPattern name pos <*> mkSumPatterns' (undefined :: proxy es) (pos + 1) (names ++ [name])

mkSumPatterns :: forall (es :: [Type]). MkSumPatterns es => TH.Q [TH.Dec]
mkSumPatterns = mkSumPatterns' (undefined :: proxy es) 0 []

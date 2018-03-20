module Data.Kore.Datastructures.EmptyTestable where

class EmptyTestable c where
    isEmpty :: c -> Bool
    empty :: c

{-|
Module      : Kore.Step.PatternAttributes
Description : Tools for using pattern attributes in step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.PatternAttributes
    ( isConstructorLikeTop
    ) where

import Data.Either
    ( isRight
    )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive

import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Proof.Functional

data PartialPatternProof proof
    = Descend proof
    | DoNotDescend proof
  deriving Functor

-- Tells whether the pattern is a built-in constructor-like pattern
isPreconstructedPattern
    :: err
    -> Recursive.Base (TermLike variable) pat
    -> Either err (PartialPatternProof (FunctionalProof variable))
isPreconstructedPattern err (_ :< pattern') =
    case pattern' of
        DomainValueF domain ->
            (Right . Descend) (FunctionalDomainValue $ () <$ domain)
        BuiltinF domain ->
            (Right . Descend) (FunctionalBuiltin $ () <$ domain)
        StringLiteralF (Const str) ->
            Right $ DoNotDescend $ FunctionalStringLiteral str
        _ -> Left err

{-|@isConstructorLikeTop@ checks whether the given 'Pattern' is topped in a
constructor / syntactic sugar for a constructor (literal / domain value)
construct.
-}
isConstructorLikeTop
    :: SmtMetadataTools Attribute.Symbol
    -> Recursive.Base (TermLike variable) pat
    -> Bool
isConstructorLikeTop _tools base@(_ :< pattern') =
    case pattern' of
        ApplySymbolF ap ->
            Symbol.isConstructor patternHead
          where
            patternHead = applicationSymbolOrAlias ap
        _ -> isRight (isPreconstructedPattern undefined base)


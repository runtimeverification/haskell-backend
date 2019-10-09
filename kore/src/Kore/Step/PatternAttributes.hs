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
    ( isConstructorLikePattern
    , isConstructorLikeTop
    , isConstructorModuloLikePattern
    ) where

import Data.Either
    ( isRight
    )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import Data.Reflection
    ( give
    )

import qualified Kore.Attribute.Symbol as Attribute
import Kore.Builtin.Attributes
    ( isConstructorModulo_
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Proof.Functional
import Kore.Step.PatternAttributesError
    ( ConstructorLikeError (..)
    )

{-| Checks whether a pattern is constructor-like or not and, if it is,
    returns a proof certifying that.
-}
isConstructorLikePattern
    :: SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> Either ConstructorLikeError [ConstructorLikeProof]
isConstructorLikePattern tools =
    provePattern (checkConstructorLikeHead tools)

{-| Checks whether a pattern is constructor-like, including
    constructors modulo associativity, commutativity and neutral element.
    If it is, returns a proof certifying that.
-}
isConstructorModuloLikePattern
    :: Show variable
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> Either ConstructorLikeError [ConstructorLikeProof]
isConstructorModuloLikePattern tools =
    provePattern (checkConstructorModuloLikeHead tools)

data PartialPatternProof proof
    = Descend proof
    | DoNotDescend proof
  deriving Functor

provePattern
    ::  (  Recursive.Base (TermLike variable) (Either error [proof])
        -> Either error (PartialPatternProof proof)
        )
    -> TermLike variable
    -> Either error [proof]
provePattern levelProver =
    Recursive.fold reduceM
  where
    reduceM base = do
        wrappedProof <- levelProver base
        case wrappedProof of
            DoNotDescend proof -> return [proof]
            Descend proof -> do
                proofs <- concat <$> sequence base
                return (proof : proofs)

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

checkConstructorLikeHead
    :: SmtMetadataTools Attribute.Symbol
    -> Recursive.Base (TermLike variable) a
    -> Either
        ConstructorLikeError
        (PartialPatternProof ConstructorLikeProof)
checkConstructorLikeHead _tools base@(_ :< pattern') =
    case pattern' of
        ApplySymbolF Application { applicationSymbolOrAlias }
          | isConstructor || isSortInjection ->
            return (Descend ConstructorLikeProof)
          where
            (isConstructor, isSortInjection) =
                ((,) <$> Symbol.isConstructor <*> Symbol.isSortInjection)
                    applicationSymbolOrAlias
        VariableF _ ->
            return (Descend ConstructorLikeProof)
        _ | Right _ <- isPreconstructedPattern undefined base ->
            return (DoNotDescend ConstructorLikeProof)
          | otherwise -> Left NonConstructorLikeHead

checkConstructorModuloLikeHead
    :: (Show a, Show variable)
    => SmtMetadataTools Attribute.Symbol
    -> Recursive.Base (TermLike variable) a
    -> Either
        ConstructorLikeError
        (PartialPatternProof ConstructorLikeProof)
checkConstructorModuloLikeHead tools base@(_ :< pattern') =
    case checkConstructorLikeHead tools base of
        r@(Right _) -> r
        Left _ ->
            case pattern' of
                ApplySymbolF Application { applicationSymbolOrAlias }
                  | isConstructorModulo -> return (Descend ConstructorLikeProof)
                  where
                    isConstructorModulo =
                        give tools isConstructorModulo_ applicationSymbolOrAlias
                _ -> Left NonConstructorLikeHead

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
    , isFunctionPattern
    , isFunctionalPattern
    , isTotalPattern
    , mapFunctionalProofVariables
    ) where

import           Control.Exception
                 ( assert )
import           Control.Lens
                 ( Prism )
import qualified Control.Lens as Lens
import           Data.Either
                 ( isRight )
import           Data.Functor.Foldable
                 ( cata )

import           Kore.AST.Common
                 ( Application (..), DomainValue (..), Pattern (..),
                 PureMLPattern, SymbolOrAlias (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Proof.Functional
import           Kore.Step.PatternAttributesError
                 ( FunctionError (..), FunctionalError (..), TotalError (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..), isTotal )

functionalProofVars
    :: Prism
         (FunctionalProof level variableFrom)
         (FunctionalProof level variableTo)
         (variableFrom level)
         (variableTo level)
functionalProofVars = Lens.prism FunctionalVariable isVar
  where
    isVar (FunctionalVariable v) = Right v
    isVar (FunctionalDomainValue dv) = Left (FunctionalDomainValue dv)
    isVar (FunctionalHead sym) = Left (FunctionalHead sym)
    isVar (FunctionalStringLiteral str) = Left (FunctionalStringLiteral str)
    isVar (FunctionalCharLiteral char) = Left (FunctionalCharLiteral char)

{-| 'mapFunctionalProofVariables' replaces all variables in a 'FunctionalProof'
using the provided mapping.
-}
mapFunctionalProofVariables
    :: (variableFrom level -> variableTo level)
    -> FunctionalProof level variableFrom
    -> FunctionalProof level variableTo
mapFunctionalProofVariables mapper = Lens.over functionalProofVars mapper

{-| checks whether a pattern is functional or not and, if it is, returns a proof
    certifying that.
-}
isFunctionalPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (FunctionalError level) [FunctionalProof level variable]
isFunctionalPattern tools =
    provePattern (checkFunctionalHead tools)

{-| checks whether a pattern is non-bottom or not and, if it is, returns a proof
    certifying that.
-}
isTotalPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (TotalError level) [TotalProof level variable]
isTotalPattern tools =
    provePattern (checkTotalHead tools)

data PartialPatternProof proof
    = Descend proof
    | DoNotDescend proof
  deriving Functor

provePattern
    ::  (  Pattern level variable (Either error [proof])
        -> Either error (PartialPatternProof proof)
        )
    -> PureMLPattern level variable
    -> Either error [proof]
provePattern levelProver =
    cata reduceM
  where
    reduceM patt = do
        wrappedProof <- levelProver patt
        case wrappedProof of
            DoNotDescend proof -> return [proof]
            Descend proof -> do
                proofs <- concat <$> sequence patt
                return (proof : proofs)

-- Tells whether the pattern is a built-in constructor-like pattern
isPreconstructedPattern
    :: err
    -> Pattern level variable pat
    -> Either err (PartialPatternProof (FunctionalProof level variable))
isPreconstructedPattern
    _
    (DomainValuePattern dv@DomainValue { domainValueChild })
  =
    (Right . Descend)
        (FunctionalDomainValue dv
            { domainValueChild = () <$ domainValueChild }
        )
isPreconstructedPattern _ (StringLiteralPattern str) =
    Right (DoNotDescend (FunctionalStringLiteral str))
isPreconstructedPattern _ (CharLiteralPattern str) =
    Right (DoNotDescend (FunctionalCharLiteral str))
isPreconstructedPattern err _ = Left err

checkFunctionalHead
    :: MetadataTools level StepperAttributes
    -> Pattern level variable a
    -> Either
        (FunctionalError level)
        (PartialPatternProof (FunctionalProof level variable))
checkFunctionalHead _ (VariablePattern v) =
    Right (DoNotDescend (FunctionalVariable v))
checkFunctionalHead tools (ApplicationPattern ap)
    | isFunctional (MetadataTools.symAttributes tools patternHead) =
        return (Descend (FunctionalHead patternHead))
    | isSortInjection (MetadataTools.symAttributes tools patternHead) =
        assert (MetadataTools.isSubsortOf tools sortFrom sortTo)
        $ return (Descend (FunctionalHead patternHead))
    | otherwise = Left (NonFunctionalHead patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
    [sortFrom, sortTo] = symbolOrAliasParams patternHead
checkFunctionalHead _ p = isPreconstructedPattern NonFunctionalPattern p

{-|@isConstructorLikeTop@ checks whether the given 'Pattern' is topped in a
constructor / syntactic sugar for a constructor (literal / domain value)
construct.
-}
isConstructorLikeTop
    :: MetadataTools level StepperAttributes
    -> Pattern level variable pat
    -> Bool
isConstructorLikeTop tools (ApplicationPattern ap) =
    isConstructor (MetadataTools.symAttributes tools patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
isConstructorLikeTop _ p = isRight (isPreconstructedPattern undefined p)

{-| checks whether a pattern is function-like or not and, if it is, returns
    a proof certifying that.
-}
isFunctionPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (FunctionError level) [FunctionProof level variable]
isFunctionPattern tools =
    provePattern (checkFunctionHead tools)

checkFunctionHead
    :: MetadataTools level StepperAttributes
    -> Pattern level variable a
    -> Either
        (FunctionError level)
        (PartialPatternProof (FunctionProof level variable))
checkFunctionHead tools (ApplicationPattern ap)
  | isFunction (MetadataTools.symAttributes tools patternHead) =
    Right (Descend (FunctionHead patternHead))
  where
    patternHead = applicationSymbolOrAlias ap
checkFunctionHead tools patt =
    case checkFunctionalHead tools patt of
        Right proof -> Right (FunctionProofFunctional <$> proof)
        Left (NonFunctionalHead patternHead) ->
            Left (NonFunctionHead patternHead)
        Left NonFunctionalPattern -> Left NonFunctionPattern

checkTotalHead
    :: MetadataTools level StepperAttributes
    -> Pattern level variable a
    -> Either
        (TotalError level)
        (PartialPatternProof (TotalProof level variable))
checkTotalHead tools (ApplicationPattern ap)
  | isTotal (MetadataTools.symAttributes tools patternHead) =
    Right (Descend (TotalHead patternHead))
  where
    patternHead = applicationSymbolOrAlias ap
checkTotalHead tools patt =
    case checkFunctionalHead tools patt of
        Right proof -> Right (TotalProofFunctional <$> proof)
        Left (NonFunctionalHead patternHead) ->
            Left (NonTotalHead patternHead)
        Left NonFunctionalPattern -> Left NonTotalPattern

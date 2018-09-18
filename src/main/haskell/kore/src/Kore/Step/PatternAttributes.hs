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
    ( FunctionProof(..)
    , FunctionalProof(..)
    , isConstructorLikeTop
    , isFunctionPattern
    , isFunctionalPattern
    , isTotalPattern
    , mapFunctionalProofVariables
    ) where

import Control.Lens
import Data.Either
       ( isRight )
import Data.Functor.Foldable
       ( cata )

import           Kore.AST.Common
                 ( Application (..), CharLiteral, DomainValue, Pattern (..),
                 StringLiteral, SymbolOrAlias, Variable )
import           Kore.AST.MetaOrObject
                 ( Meta )
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.PatternAttributesError
                 ( FunctionError (..), FunctionalError (..), TotalError (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..), isTotal )

-- |'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionalProof level variable
    = FunctionalVariable (variable level)
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalDomainValue (DomainValue level (PureMLPattern Meta Variable))
    -- ^Domain values are functional as ther represent one value in the model.
    | FunctionalHead (SymbolOrAlias level)
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    | FunctionalStringLiteral StringLiteral
    -- ^A string literal is the repeated application of functional constructors.
    | FunctionalCharLiteral CharLiteral
    -- ^A char literal is a functional constructor without arguments.
  deriving (Eq, Show)

-- |'FunctionProof' is used for providing arguments that a pattern is
-- function-like.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional and function symbols and
-- variables.
-- Hence, a proof that a pattern is function-like is a list of 'FunctionProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionProof level variable
    = FunctionProofFunctional (FunctionalProof level variable)
    -- ^ A functional component is also function-like.
    | FunctionHead (SymbolOrAlias level)
    -- ^Head of a partial function.
  deriving (Eq, Show)

-- |'TotalProof' is used for providing arguments that a pattern is
-- total/not bottom.  Currently we only support arguments stating that a
-- pattern is functional or a constructor.
-- Hence, a proof that a pattern is total is a list of 'TotalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data TotalProof level variable
    = TotalProofFunctional (FunctionalProof level variable)
    -- ^A functional component is also total.
    | TotalHead (SymbolOrAlias level)
    -- ^Head of a total symbol.
  deriving (Eq, Show)

functionalProofVars
    :: Prism
         (FunctionalProof level variableFrom)
         (FunctionalProof level variableTo)
         (variableFrom level)
         (variableTo level)
functionalProofVars = prism FunctionalVariable isVar
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
mapFunctionalProofVariables mapper = functionalProofVars %~ mapper

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
isPreconstructedPattern _ (DomainValuePattern dv) =
    Right (DoNotDescend (FunctionalDomainValue dv))
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
checkFunctionalHead tools (ApplicationPattern ap) =
    if isFunctional (MetadataTools.symAttributes tools patternHead)
        then return (Descend (FunctionalHead patternHead))
        else Left (NonFunctionalHead patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
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

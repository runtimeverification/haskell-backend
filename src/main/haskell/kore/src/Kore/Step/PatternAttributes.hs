{-|
Module      : Kore.Step.PatternAttributes
Description : Tools for using pattern attributes in step execution
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.PatternAttributes
    ( FunctionProof(..)
    , FunctionalProof(..)
    , isFunctionPattern
    , isFunctionalPattern
    , mapFunctionalProofVariables
    ) where

import Control.Lens
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
                 ( FunctionError (..), FunctionalError (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )

-- |'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionalProof level domain variable
    = FunctionalVariable (variable level)
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalDomainValue (DomainValue level (PureMLPattern Meta domain Variable))
    -- ^Domain values are functional as ther represent one value in the model.
    | FunctionalHead (SymbolOrAlias level)
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    | FunctionalStringLiteral StringLiteral
    -- ^A string literal is the repeated application of functional constructors.
    | FunctionalCharLiteral CharLiteral
    -- ^A char literal is a functional constructor without arguments.
  deriving (Eq, Show)

functionalProofVars
    :: Prism
         (FunctionalProof level domain variableFrom)
         (FunctionalProof level domain variableTo)
         (variableFrom level)
         (variableTo level)
functionalProofVars = prism FunctionalVariable isVar
  where
    isVar (FunctionalVariable v) = Right v
    isVar (FunctionalDomainValue dv) = Left (FunctionalDomainValue dv)
    isVar (FunctionalHead sym) = Left (FunctionalHead sym)
    isVar (FunctionalStringLiteral str) = Left (FunctionalStringLiteral str)
    isVar (FunctionalCharLiteral char) = Left (FunctionalCharLiteral char)

-- |'FunctionProof' is used for providing arguments that a pattern is
-- function-like.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional and function symbols and
-- variables.
-- Hence, a proof that a pattern is function-like is a list of 'FunctionProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionProof level domain variable
    = FunctionProofFunctional (FunctionalProof level domain variable)
    -- ^ A functional component is also function-like.
    | FunctionHead (SymbolOrAlias level)
    -- ^Head of a partial function.
  deriving (Eq, Show)

{-| 'mapFunctionalProofVariables' replaces all variables in a 'FunctionalProof'
using the provided mapping.
-}
mapFunctionalProofVariables
    :: (variableFrom level -> variableTo level)
    -> FunctionalProof level domain variableFrom
    -> FunctionalProof level domain variableTo
mapFunctionalProofVariables mapper = functionalProofVars %~ mapper

{-| checks whether a pattern is functional or not and, if it is, returns a proof
    certifying that.
-}
isFunctionalPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Either (FunctionalError level) [FunctionalProof level domain variable]
isFunctionalPattern tools = cata  reduceM
  where
    reduceM patt = do
        proof <- checkFunctionalHead tools patt
        proofs <- concat <$> sequence patt
        return (proof : proofs)

checkFunctionalHead
    :: MetadataTools level StepperAttributes
    -> Pattern level domain variable a
    -> Either (FunctionalError level) (FunctionalProof level domain variable)
checkFunctionalHead _ (DomainValuePattern dv) =
    Right (FunctionalDomainValue dv)
checkFunctionalHead _ (StringLiteralPattern str) =
    Right (FunctionalStringLiteral str)
checkFunctionalHead _ (CharLiteralPattern str) =
    Right (FunctionalCharLiteral str)
checkFunctionalHead _ (VariablePattern v) =
    Right (FunctionalVariable v)
checkFunctionalHead tools (ApplicationPattern ap) =
    if isFunctional (MetadataTools.attributes tools patternHead)
        then return (FunctionalHead patternHead)
        else Left (NonFunctionalHead patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
checkFunctionalHead _ _ = Left NonFunctionalPattern

{-| checks whether a pattern is function-like or not and, if it is, returns
    a proof certifying that.
-}
isFunctionPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Either (FunctionError level) [FunctionProof level domain variable]
isFunctionPattern tools = cata reduceM
  where
    reduceM patt = do
        proof <- checkFunctionHead tools patt
        proofs <- concat <$> sequence patt
        return (proof : proofs)

checkFunctionHead
    :: MetadataTools level StepperAttributes
    -> Pattern level domain variable a
    -> Either (FunctionError level) (FunctionProof level domain variable)
checkFunctionHead tools (ApplicationPattern ap)
  | isFunction (MetadataTools.attributes tools patternHead) =
    Right (FunctionHead patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
checkFunctionHead tools patt =
    case checkFunctionalHead tools patt of
        Right proof -> Right (FunctionProofFunctional proof)
        Left (NonFunctionalHead patternHead) ->
            Left (NonFunctionHead patternHead)
        Left NonFunctionalPattern -> Left NonFunctionPattern

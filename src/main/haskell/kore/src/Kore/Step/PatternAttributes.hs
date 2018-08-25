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

import           Data.Functor.Traversable
                 ( fixBottomUpVisitorM )
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

{-| 'mapFunctionalProofVariables' replaces all variables in a 'FunctionalProof'
using the provided mapping.
-}
mapFunctionalProofVariables
    :: (variableFrom level -> variableTo level)
    -> FunctionalProof level variableFrom
    -> FunctionalProof level variableTo
mapFunctionalProofVariables mapper (FunctionalVariable variable) =
    FunctionalVariable (mapper variable)
mapFunctionalProofVariables _ (FunctionalDomainValue dv) =
    FunctionalDomainValue dv
mapFunctionalProofVariables _ (FunctionalHead functionalHead) =
    FunctionalHead functionalHead
mapFunctionalProofVariables _ (FunctionalStringLiteral literal) =
    FunctionalStringLiteral literal
mapFunctionalProofVariables _ (FunctionalCharLiteral literal) =
    FunctionalCharLiteral literal

{-| checks whether a pattern is functional or not and, if it is, returns a proof
    certifying that.
-}
isFunctionalPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (FunctionalError level) [FunctionalProof level variable]
isFunctionalPattern tools = fixBottomUpVisitorM reduceM
  where
    reduceM patt = do
        (proof, proofs) <- functionalReduce tools patt
        return (proof : proofs)

functionalReduce
    :: MetadataTools level StepperAttributes
    -> Pattern level variable [proof]
    -> Either (FunctionalError level) (FunctionalProof level variable, [proof])
functionalReduce _ (DomainValuePattern dv) =
    Right (FunctionalDomainValue dv, [])
functionalReduce _ (StringLiteralPattern str) =
    Right (FunctionalStringLiteral str, [])
functionalReduce _ (CharLiteralPattern str) =
    Right (FunctionalCharLiteral str, [])
functionalReduce _ (VariablePattern v) =
    Right (FunctionalVariable v, [])
functionalReduce tools (ApplicationPattern ap) =
    if isFunctional (MetadataTools.attributes tools patternHead)
        then return (FunctionalHead patternHead, concat proofs)
        else Left (NonFunctionalHead patternHead)
  where
    patternHead = applicationSymbolOrAlias ap
    proofs = applicationChildren ap
functionalReduce _ _ = Left NonFunctionalPattern

{-| checks whether a pattern is function-like or not and, if it is, returns
    a proof certifying that.
-}
isFunctionPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (FunctionError level) [FunctionProof level variable]
isFunctionPattern tools = fixBottomUpVisitorM reduceM
  where
    reduceM patt = do
        (proof, proofs) <- functionReduce tools patt
        return (proof : proofs)

functionReduce
    :: MetadataTools level StepperAttributes
    -> Pattern level variable [proof]
    -> Either (FunctionError level) (FunctionProof level variable, [proof])
functionReduce tools (ApplicationPattern ap)
  | isFunction (MetadataTools.attributes tools patternHead) =
    Right (FunctionHead patternHead, concat proofs)
  where
    patternHead = applicationSymbolOrAlias ap
    proofs = applicationChildren ap
functionReduce tools patt =
    case functionalReduce tools patt of
        Right (proof, proofs) -> Right (FunctionProofFunctional proof, proofs)
        Left (NonFunctionalHead patternHead) ->
            Left (NonFunctionHead patternHead)
        Left NonFunctionalPattern -> Left NonFunctionPattern

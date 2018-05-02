module Data.Kore.Unification.Unifier
    ( simplifyAnd
    , MetadataTools (..)
    , UnificationProof (..)
    , unificationSolutionToPurePattern
    , UnificationSolution (..)
    , UnificationError (..)
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals

import           Data.Fix
import           Data.Function            (on)
import           Data.List                (sortBy)

data MetadataTools level = MetadataTools
    { isConstructor    :: SymbolOrAlias level -> Bool
    , isFunctional     :: SymbolOrAlias level -> Bool
    , getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

data UnificationSolution level = UnificationSolution
    { unificationSolutionTerm        :: !(CommonPurePattern level)
    , unificationSolutionConstraints :: ![( Variable level
                                          , CommonPurePattern level)]
    }
  deriving (Eq)


unificationSolutionToPurePattern
    :: MetadataTools level
    -> UnificationSolution level
    -> CommonPurePattern level
unificationSolutionToPurePattern tools ucp =
    foldr
        (andEquals
            (getPatternResultSort (getResultSort tools) (unFix unifiedTerm)))
        unifiedTerm
        (unificationSolutionConstraints ucp)
  where
    unifiedTerm = unificationSolutionTerm ucp
    andEquals sort (var, p) second = Fix $ AndPattern And
        { andSort = sort
        , andFirst = Fix $ EqualsPattern Equals
            { equalsOperandSort = variableSort var
            , equalsResultSort = sort
            , equalsFirst = Fix $ VariablePattern var
            , equalsSecond = p
            }
        , andSecond = second
        }

data UnificationProof = UnificationProof
  deriving (Eq)

data UnificationError
    = ConstructorClash
    | NonConstructorHead
    | NonFunctionalPattern
    | UnsupportedPatterns
  deriving (Eq)

isFunctionalPattern
    :: MetadataTools level -> PureMLPattern level variable -> Maybe Bool
isFunctionalPattern tools = fixBottomUpVisitorM reduceM
  where
    reduceM (VariablePattern _) = return True
    reduceM (ApplicationPattern ap) = return $
        foldr (&&)
            (isFunctional tools (applicationSymbolOrAlias ap))
            (applicationChildren ap)
    reduceM _ = Nothing

simplifyAnd
    :: MetadataTools level
    -> PureMLPattern level Variable
    -> Either UnificationError (UnificationSolution level, UnificationProof)
simplifyAnd tools =
    fixTopDownVisitor (preTransform tools) postTransform

preTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level Variable
    -> Either
        (Either UnificationError (UnificationSolution level, UnificationProof))
        (UnFixedPureMLPattern level Variable)
preTransform tools (AndPattern ap) = if left == right
    then Left $ Right
        ( UnificationSolution
            { unificationSolutionTerm = left
            , unificationSolutionConstraints = []
            }
        , UnificationProof
        )
    else case (unFix left, unFix right) of
        (VariablePattern vp, _) ->
            Left (mlProposition5243 tools vp right)

        (_, VariablePattern vp) -> -- add commutativity here
            Left (mlProposition5243 tools vp left)
        (ApplicationPattern ap1, ApplicationPattern ap2) ->
            let
                head1 = applicationSymbolOrAlias ap1
                head2 = applicationSymbolOrAlias ap2
            in
                if isConstructor tools head1
                    then if head1 == head2
                        then Right
                            $ ApplicationPattern Application
                                { applicationSymbolOrAlias = head1
                                , applicationChildren =
                                    Fix . AndPattern
                                        <$> zipWith3 And
                                            (getArgumentSorts tools head1)
                                            (applicationChildren ap1)
                                            (applicationChildren ap2)
                                }
                        else if isConstructor tools head2
                            then Left $ Left ConstructorClash
                            else Left $ Left NonConstructorHead
                    else Left $ Left NonConstructorHead
        _ -> Left $ Left UnsupportedPatterns
  where
    left = andFirst ap
    right = andSecond ap

mlProposition5243
    :: MetadataTools level
    -> Variable level
    -- ^variable pattern
    -> PureMLPattern level Variable
    -- ^functional (term) pattern
    -> Either UnificationError (UnificationSolution level, UnificationProof)
mlProposition5243
    tools
    v
    functionalPattern
  = case isFunctionalPattern tools functionalPattern of
        Just True -> Right --Matching Logic 5.24 (3)
            ( UnificationSolution
                { unificationSolutionTerm        = functionalPattern
                , unificationSolutionConstraints = [ (v, functionalPattern) ]
                }
            , UnificationProof
            )
        _ -> Left NonFunctionalPattern

postTransform
    :: Pattern level Variable
        (Either UnificationError (UnificationSolution level, UnificationProof))
    -> Either UnificationError (UnificationSolution level, UnificationProof)
postTransform (ApplicationPattern ap) =
    case sequenceA (applicationChildren ap) of
        Left err -> Left err
        Right children ->
            let (subSolutions, subProofs) = unzip children in
                Right
                    ( UnificationSolution
                        { unificationSolutionTerm = Fix $ ApplicationPattern ap
                            { applicationChildren =
                                    map unificationSolutionTerm subSolutions
                            }
                        , unificationSolutionConstraints =
                            sortBy (compare `on` fst)
                                (concatMap
                                    unificationSolutionConstraints
                                    subSolutions
                                )
                        }
                    , UnificationProof
                    )

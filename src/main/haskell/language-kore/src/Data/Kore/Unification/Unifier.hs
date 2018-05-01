module Data.Kore.Unification.Unifier
    ( simplifyAnd
    , MetadataTools (..)
    ) where

import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals

data MetadataTools level = MetadataTools
    { isConstructor    :: SymbolOrAlias level -> Bool
    , isFunctional     :: SymbolOrAlias level -> Bool
    , getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

data UnificationProof = UnificationProof

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
    -> PureMLPattern level Variable
simplifyAnd tools =
    fixTopDownTransformer (preTransform tools) (postTransform tools)

preTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level Variable
    -> Either
        (UnFixedPureMLPattern level Variable)
        (UnFixedPureMLPattern level Variable)
preTransform tools (AndPattern ap) =
    case (unFix left, unFix right) of
        (VariablePattern vp, _) ->
            Left (mlProposition5243 tools left right patternSort)
        (_, VariablePattern vp) -> -- add commutativity here
            Left (mlProposition5243 tools right left patternSort)
        (ApplicationPattern ap1, ApplicationPattern ap2) ->
            let
                head1 = applicationSymbolOrAlias ap1
                head2 = applicationSymbolOrAlias ap2
            in
                if head1 == head2 && isConstructor tools head1
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
                    else undefined
  where
    left = andFirst ap
    right = andSecond ap
    patternSort = andSort ap

mlProposition5243
    :: MetadataTools level
    -> PureMLPattern level Variable
    -- ^variable pattern
    -> PureMLPattern level Variable
    -- ^functional (term) pattern
    -> Sort level
    -- ^sort of the patterns
    -> UnFixedPureMLPattern level Variable
mlProposition5243
    tools
    variablePattern@(Fix (VariablePattern _))
    functionalPattern
    patternSort
  = case isFunctionalPattern tools functionalPattern of
        Just True -> --Matching Logic 5.24 (3)
            AndPattern And
                { andSort = patternSort
                , andFirst = variablePattern
                , andSecond =
                    Fix $ EqualsPattern Equals
                        { equalsOperandSort = patternSort
                        , equalsResultSort = patternSort
                        , equalsFirst = variablePattern
                        , equalsSecond = functionalPattern
                        }
                }

postTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level Variable
    -> UnFixedPureMLPattern level Variable
postTransform tools (ApplicationPattern ap) =
    AndPattern And
        { andSort = patternSort
        , andFirst = Fix
            $ ApplicationPattern ap
                { applicationChildren = map fst splittedConjuncts }
        , andSecond = case liftedConjuncts of
            [] -> Fix (TopPattern (Top patternSort))
            (c:cs) ->
                foldr (\ l r -> Fix (AndPattern (And patternSort l r))) c cs
        }
  where
    patternSort = getResultSort tools (applicationSymbolOrAlias ap)
    children = applicationChildren ap
    splittedConjuncts = map splitConjunct children
    splitConjunct (Fix (AndPattern andP)) = (andFirst andP, andSecond andP)
    liftedConjuncts =
        map (upgradeConjunctsToSort patternSort . snd) splittedConjuncts

upgradeConjunctsToSort
    :: Sort level -> PureMLPattern level var -> PureMLPattern level var
upgradeConjunctsToSort sort = fixTopDownVisitor preprocess Fix
  where
    preprocess (AndPattern ap) = Right $ AndPattern ap { andSort = sort }
    preprocess (EqualsPattern ep) =
        Left . Fix $ EqualsPattern ep { equalsResultSort = sort }

module Data.Kore.Unification.Unifier
    ( simplifyAnd
    ) where

import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals

data MetadataTools level = MetadataTools
    { isConstructor :: SymbolOrAlias level -> Bool
    , isFunctional  :: SymbolOrAlias level -> Bool
    }

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
    -> PureMLPattern level variable
    -> PureMLPattern level variable
simplifyAnd tools =
    fixTopDownTransformer (preTransform tools) (postTransform tools)

preTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level variable
    -> Either
        (UnFixedPureMLPattern level variable)
        (UnFixedPureMLPattern level variable)
preTransform tools (AndPattern ap) =
    case (unFix left, unFix right) of
        (VariablePattern _, _) ->
            case isFunctionalPattern tools right of
                Just True -> --Matching Logic 5.24 (3)
                    Left
                        (AndPattern ap
                            { andSecond = undefined
                            }
                        )
  where
    left = andFirst ap
    right = andSecond ap

postTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level variable
    -> UnFixedPureMLPattern level variable
postTransform = undefined

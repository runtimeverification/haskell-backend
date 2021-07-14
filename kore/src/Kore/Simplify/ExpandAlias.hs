{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Simplify.ExpandAlias (
    expandSingleAlias,
    matchExpandAlias,
    substituteInAlias,
    UnifyExpandAlias (..),
) where

import qualified Data.Map.Strict as Map
import Kore.Internal.Alias (
    Alias (..),
 )
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    Variable (..),
    VariableName,
    fromVariableName,
    mapSomeVariableName,
    mapVariables,
    pattern ApplyAlias_,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Substitute
import Prelude.Kore

data UnifyExpandAlias = UnifyExpandAlias
    { term1, term2 :: !(TermLike RewritingVariableName)
    }

-- | Matches two terms when either is an alias.
matchExpandAlias ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyExpandAlias
matchExpandAlias t1 t2 =
    case (expandSingleAlias t1, expandSingleAlias t2) of
        (Nothing, Nothing) -> Nothing
        (t1', t2') ->
            let term1 = fromMaybe t1 t1'
                term2 = fromMaybe t2 t2'
             in Just UnifyExpandAlias{term1, term2}
{-# INLINE matchExpandAlias #-}

expandSingleAlias ::
    TermLike RewritingVariableName ->
    Maybe (TermLike RewritingVariableName)
expandSingleAlias =
    \case
        ApplyAlias_ alias children -> pure $ substituteInAlias alias children
        _ -> Nothing

-- TODO(Vladimir): Check aliases such that the intersection of alias variables
-- with the *bounded* variables in the rhs is empty (because we can't currently
-- handle things like \mu.
substituteInAlias ::
    InternalVariable variable =>
    Alias (TermLike VariableName) ->
    [TermLike variable] ->
    TermLike variable
substituteInAlias Alias{aliasLeft, aliasRight} children =
    assert (length aliasLeft == length children) $
        substitute substitutionMap $
            mapVariables (pure fromVariableName) aliasRight
  where
    aliasLeft' =
        mapSomeVariableName (pure fromVariableName) . variableName
            <$> aliasLeft
    substitutionMap = Map.fromList $ zip aliasLeft' children

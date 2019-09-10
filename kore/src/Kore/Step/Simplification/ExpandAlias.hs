{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Simplification.ExpandAlias
    ( expandAlias
    ) where

import           Control.Error
                 ( MaybeT )
import           Control.Error.Util
                 ( nothing )
import qualified Data.Map as Map

import           Kore.Internal.Alias
                 ( Alias (..) )
import           Kore.Internal.Pattern
                 ( Pattern )
import           Kore.Internal.TermLike
                 ( pattern ApplyAlias_, TermLike, Variable, substitute )
import qualified Kore.Logger as Logger
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Unify
                 ( MonadUnify )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

expandAlias
    :: forall variable unifier
    .  FreshVariable variable
    => Ord variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => MonadUnify unifier
    => Logger.WithLog Logger.LogMessage unifier
    => (   TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
       )
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
expandAlias recurse t1 t2 = do
    case (expandSingleAlias t1, expandSingleAlias t2) of
        (Nothing, Nothing) -> nothing
        (t1', t2') -> recurse (maybe t1 id t1') (maybe t2 id t2')

expandSingleAlias
    :: TermLike variable
    -> Maybe (TermLike variable)
expandSingleAlias =
    \case
        ApplyAlias_ alias children -> pure $ substituteWorker alias children
        _ -> Nothing

-- TODO(Vladimir): Check aliases such that the intersection of alias variables
-- with the *bounded* variables in the rhs is empty (because we can't currently
-- handle things like \mu.
substituteWorker
    :: Alias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable
substituteWorker Alias { aliasLeft, aliasRight } children =
    substitute
        substitutionMap
        aliasRight
  where
    substitutionMap = Map.fromList $ zip aliasLeft children

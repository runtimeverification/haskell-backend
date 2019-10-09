{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Simplification.ExpandAlias
    ( expandAlias
    , substituteInAlias
    ) where

import Control.Error
    ( MaybeT
    )
import Control.Error.Util
    ( nothing
    )
import Control.Exception
    ( assert
    )
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )

import Kore.Internal.Alias
    ( Alias (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
    ( pattern ApplyAlias_
    , SubstitutionVariable
    , TermLike
    , Variable
    , mapVariables
    , substitute
    )
import qualified Kore.Logger as Logger
import Kore.Syntax.Variable
    ( SortedVariable (..)
    )
import Kore.Unification.Unify
    ( MonadUnify
    )

expandAlias
    :: forall variable unifier
    .  SubstitutionVariable variable
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
        (t1', t2') -> recurse (fromMaybe t1 t1') (fromMaybe t2 t2')

expandSingleAlias
    :: SubstitutionVariable variable
    => TermLike variable
    -> Maybe (TermLike variable)
expandSingleAlias =
    \case
        ApplyAlias_ alias children -> pure $ substituteInAlias alias children
        _ -> Nothing

-- TODO(Vladimir): Check aliases such that the intersection of alias variables
-- with the *bounded* variables in the rhs is empty (because we can't currently
-- handle things like \mu.
substituteInAlias
    :: SubstitutionVariable variable
    => Alias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable
substituteInAlias Alias { aliasLeft, aliasRight } children =
    assert (length aliasLeft == length children)
        $ substitute
            substitutionMap
            (mapVariables fromVariable aliasRight)
  where
    substitutionMap =
        Map.fromList $ zip (fmap fromVariable <$> aliasLeft) children

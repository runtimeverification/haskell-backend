{-|
Module      : Kore.AST.Lens
Description : Lenses into Kore patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
-}

module Kore.AST.Lens
    ( localInPattern
    , inPath
    , isObviouslyPredicate
    , resultSort
    ) where

import           Control.Lens hiding
                 ( (:<) )
import qualified Data.Functor.Foldable as Recursive

import Kore.AST.Pure
import Kore.Domain.Class

patternLens
    ::  forall f domain variable1 variable2 annotation
    .   (Applicative f, Domain domain, Traversable domain)
    => (Sort Object -> f (Sort Object))  -- ^ Operand sorts
    -> (Sort Object -> f (Sort Object))
    -- ^ Result sorts, and operand sorts when the two are equal
    -> (variable1 Object -> f (variable2 Object))  -- ^ Variables
    ->  (  PurePattern Object domain variable1 annotation
        -> f (PurePattern Object domain variable2 annotation)
        )
        -- ^ Children
    ->  (  PurePattern Object domain variable1 annotation
        -> f (PurePattern Object domain variable2 annotation)
        )
patternLens
    lensOperandSort   -- input sort
    lensResultSort   -- result sort, and operand sort when they are identical
    lensVariable -- variable
    lensChild   -- child
  = \(Recursive.project -> ann :< pat) ->
    Recursive.embed . (ann :<) <$> patternLensWorker pat
  where
    patternLensWorker =
        \case
            AndPattern and0 -> AndPattern <$> patternLensAnd and0
            BottomPattern bot0 -> BottomPattern <$> patternLensBottom bot0
            CeilPattern ceil0 -> CeilPattern <$> patternLensCeil ceil0
            DomainValuePattern dv0 ->
                DomainValuePattern <$> patternLensDomain dv0
            EqualsPattern eq0 -> EqualsPattern <$> patternLensEquals eq0
            ExistsPattern ex0 -> ExistsPattern <$> patternLensExists ex0
            FloorPattern flr0 -> FloorPattern <$> patternLensFloor flr0
            ForallPattern fa0 -> ForallPattern <$> patternLensForall fa0
            IffPattern iff0 -> IffPattern <$> patternLensIff iff0
            ImpliesPattern imp0 -> ImpliesPattern <$> patternLensImplies imp0
            InPattern in0 -> InPattern <$> patternLensIn in0
            NextPattern next0 -> NextPattern <$> patternLensNext next0
            NotPattern not0 -> NotPattern <$> patternLensNot not0
            OrPattern or0 -> OrPattern <$> patternLensOr or0
            RewritesPattern rew0 -> RewritesPattern <$> patternLensRewrites rew0
            TopPattern top0 -> TopPattern <$> patternLensTop top0
            VariablePattern var0 -> VariablePattern <$> lensVariable var0
            ApplicationPattern app0 ->
                ApplicationPattern <$> patternLensApplication app0
            StringLiteralPattern lit -> pure (StringLiteralPattern lit)
            CharLiteralPattern lit -> pure (CharLiteralPattern lit)

    patternLensAnd And { andSort, andFirst, andSecond } =
        And
            <$> lensResultSort andSort
            <*> lensChild andFirst
            <*> lensChild andSecond

    patternLensBottom Bottom { bottomSort } =
        Bottom <$> lensResultSort bottomSort

    patternLensCeil Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        Ceil
            <$> lensOperandSort ceilOperandSort
            <*> lensResultSort ceilResultSort
            <*> lensChild ceilChild

    patternLensDomain
        :: level ~ Object
        => domain (PurePattern level domain variable1 annotation)
        -> f (domain (PurePattern level domain variable2 annotation))
    patternLensDomain =
        lensDomainValue patternLensDomainValue
      where
        patternLensDomainValue
            DomainValue
                { domainValueSort
                , domainValueChild
                }
          =
            DomainValue
                <$> lensResultSort domainValueSort
                <*> traverse lensChild domainValueChild

    patternLensEquals
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        Equals
            <$> lensOperandSort equalsOperandSort
            <*> lensResultSort equalsResultSort
            <*> lensChild equalsFirst
            <*> lensChild equalsSecond

    patternLensExists Exists { existsSort, existsVariable, existsChild } =
        Exists
            <$> lensResultSort existsSort
            <*> lensVariable existsVariable
            <*> lensChild existsChild

    patternLensFloor Floor { floorOperandSort, floorResultSort, floorChild } =
        Floor
            <$> lensOperandSort floorOperandSort
            <*> lensResultSort floorResultSort
            <*> lensChild floorChild

    patternLensForall Forall { forallSort, forallVariable, forallChild } =
        Forall
            <$> lensResultSort forallSort
            <*> lensVariable forallVariable
            <*> lensChild forallChild

    patternLensIff Iff { iffSort, iffFirst, iffSecond } =
        Iff
            <$> lensResultSort iffSort
            <*> lensChild iffFirst
            <*> lensChild iffSecond

    patternLensImplies Implies { impliesSort, impliesFirst, impliesSecond } =
        Implies
            <$> lensResultSort impliesSort
            <*> lensChild impliesFirst
            <*> lensChild impliesSecond

    patternLensIn
        In
            { inOperandSort
            , inResultSort
            , inContainedChild
            , inContainingChild
            }
      =
        In
            <$> lensOperandSort inOperandSort
            <*> lensResultSort inResultSort
            <*> lensChild inContainedChild
            <*> lensChild inContainingChild

    patternLensNext Next { nextSort, nextChild } =
        Next
            <$> lensResultSort nextSort
            <*> lensChild nextChild

    patternLensNot Not { notSort, notChild } =
        Not
            <$> lensResultSort notSort
            <*> lensChild notChild

    patternLensOr Or { orSort, orFirst, orSecond } =
        Or
            <$> lensResultSort orSort
            <*> lensChild orFirst
            <*> lensChild orSecond

    patternLensRewrites
        Rewrites
            { rewritesSort
            , rewritesFirst
            , rewritesSecond
            }
      =
        Rewrites
            <$> lensResultSort rewritesSort
            <*> lensChild rewritesFirst
            <*> lensChild rewritesSecond

    patternLensTop Top { topSort } =
        Top <$> lensResultSort topSort

    patternLensApplication
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
      =
        Application applicationSymbolOrAlias
            <$> traverse lensChild applicationChildren

-- | The sort returned by a top-level constructor.
resultSort
    :: (Domain domain, Traversable domain)
    => Traversal' (PurePattern Object domain variable annotation) (Sort Object)
resultSort = \f -> patternLens pure f pure pure

-- | All sub-expressions which are 'Pattern's.
-- Use partsOf allChildren to get a lens to a List.
allChildren
    :: (Domain domain, Traversable domain)
    => Traversal'
        (PurePattern Object domain variable annotation)
        (PurePattern Object domain variable annotation)
allChildren = patternLens pure pure pure

-- | Applies a function at an `[Int]` path.
localInPattern
    :: (MetaOrObject level, Domain domain, Traversable domain)
    => [Int]
    ->  (  PurePattern level domain variable annotation
        -> PurePattern level domain variable annotation
        )
    -> PurePattern level domain variable annotation
    -> PurePattern level domain variable annotation
localInPattern path f pat = pat & inPath path %~ f

-- | Takes an `[Int]` representing a path, and returns a lens to that position.
-- The ints represent subpatterns in the obvious way:
-- [0,1] points to b in \ceil(a /\ b), etc.
inPath
    :: (MetaOrObject level, Applicative f, Domain domain, Traversable domain)
    => [Int]
    ->  (  PurePattern level domain variable annotation
        -> f (PurePattern level domain variable annotation)
        )
    ->  (  PurePattern level domain variable annotation
        -> f (PurePattern level domain variable annotation)
        )
inPath []       = id --aka the identity lens
inPath (n : ns) = partsOf allChildren . ix n . inPath ns

-- | In practice, all the predicate patterns we use are
-- composed of =, \floor, \ceil, and \in. I haven't come
-- across a single counterexample. Thus this function can
-- probably be trusted to tell you if something is a
-- predicate. Note that `isObviouslyPredicate` and
-- `hasFlexibleHead` are NOT the same. `hasFlexibleHead` only
-- looks at the head of the pattern, it will return false
-- for `a = b /\ c = d`, whereas `isObviouslyPredicate` will
-- traverse the whole pattern and return True.
-- Also, in practice, having a flexible sort and being a predicate
-- are synonymous. But don't quote me on this.
isObviouslyPredicate
    :: Functor domain
    => PurePattern level domain variable annotation
    -> Bool
isObviouslyPredicate (Recursive.project -> _ :< pat) =
    case pat of
        -- Trivial cases
        EqualsPattern _ -> True
        InPattern _ -> True
        CeilPattern _ -> True
        FloorPattern _ -> True
        -- Non-trivial cases
        AndPattern and0 -> all isObviouslyPredicate and0
        OrPattern or0 -> all isObviouslyPredicate or0
        ImpliesPattern imp0 -> all isObviouslyPredicate imp0
        IffPattern iff0 -> all isObviouslyPredicate iff0
        NotPattern not0 -> all isObviouslyPredicate not0
        ForallPattern all0 -> all isObviouslyPredicate all0
        ExistsPattern any0 -> all isObviouslyPredicate any0
        -- Non-predicates
        _ -> False

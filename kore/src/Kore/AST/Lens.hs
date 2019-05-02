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

import Kore.Domain.Class
import Kore.Syntax

patternLens
    ::  forall f domain variable1 variable2 annotation
    .   (Applicative f, Domain domain, Traversable domain)
    => (Sort -> f Sort)  -- ^ Operand sorts
    -> (Sort -> f Sort)
    -- ^ Result sorts, and operand sorts when the two are equal
    -> (variable1 -> f variable2)  -- ^ Variables
    ->  (  Pattern domain variable1 annotation
        -> f (Pattern domain variable2 annotation)
        )
        -- ^ Children
    ->  (  Pattern domain variable1 annotation
        -> f (Pattern domain variable2 annotation)
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
            AndF and0 -> AndF <$> patternLensAnd and0
            BottomF bot0 -> BottomF <$> patternLensBottom bot0
            CeilF ceil0 -> CeilF <$> patternLensCeil ceil0
            DomainValueF dv0 ->
                DomainValueF <$> patternLensDomain dv0
            EqualsF eq0 -> EqualsF <$> patternLensEquals eq0
            ExistsF ex0 -> ExistsF <$> patternLensExists ex0
            FloorF flr0 -> FloorF <$> patternLensFloor flr0
            ForallF fa0 -> ForallF <$> patternLensForall fa0
            IffF iff0 -> IffF <$> patternLensIff iff0
            ImpliesF imp0 -> ImpliesF <$> patternLensImplies imp0
            InF in0 -> InF <$> patternLensIn in0
            NextF next0 -> NextF <$> patternLensNext next0
            NotF not0 -> NotF <$> patternLensNot not0
            OrF or0 -> OrF <$> patternLensOr or0
            RewritesF rew0 -> RewritesF <$> patternLensRewrites rew0
            TopF top0 -> TopF <$> patternLensTop top0
            VariableF var0 -> VariableF <$> lensVariable var0
            SetVariableF svar0 ->
                SetVariableF <$> patternLensSetVariable svar0
            ApplicationF app0 ->
                ApplicationF <$> patternLensApplication app0
            StringLiteralF lit -> pure (StringLiteralF lit)
            CharLiteralF lit -> pure (CharLiteralF lit)
            InhabitantF s -> pure (InhabitantF s)

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
        :: domain (Pattern domain variable1 annotation)
        -> f (domain (Pattern domain variable2 annotation))
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

    patternLensSetVariable (SetVariable variable) =
        SetVariable <$> lensVariable variable

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
    => Traversal' (Pattern domain variable annotation) Sort
resultSort = \f -> patternLens pure f pure pure

-- | All sub-expressions which are 'Pattern's.
-- Use partsOf allChildren to get a lens to a List.
allChildren
    :: (Domain domain, Traversable domain)
    => Traversal'
        (Pattern domain variable annotation)
        (Pattern domain variable annotation)
allChildren = patternLens pure pure pure

-- | Applies a function at an `[Int]` path.
localInPattern
    :: (Domain domain, Traversable domain)
    => [Int]
    ->  (  Pattern domain variable annotation
        -> Pattern domain variable annotation
        )
    -> Pattern domain variable annotation
    -> Pattern domain variable annotation
localInPattern path f pat = pat & inPath path %~ f

-- | Takes an `[Int]` representing a path, and returns a lens to that position.
-- The ints represent subpatterns in the obvious way:
-- [0,1] points to b in \ceil(a /\ b), etc.
inPath
    :: (Applicative f, Domain domain, Traversable domain)
    => [Int]
    ->  (  Pattern domain variable annotation
        -> f (Pattern domain variable annotation)
        )
    ->  (  Pattern domain variable annotation
        -> f (Pattern domain variable annotation)
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
    => Pattern domain variable annotation
    -> Bool
isObviouslyPredicate (Recursive.project -> _ :< pat) =
    case pat of
        -- Trivial cases
        EqualsF _ -> True
        InF _ -> True
        CeilF _ -> True
        FloorF _ -> True
        -- Non-trivial cases
        AndF and0 -> all isObviouslyPredicate and0
        OrF or0 -> all isObviouslyPredicate or0
        ImpliesF imp0 -> all isObviouslyPredicate imp0
        IffF iff0 -> all isObviouslyPredicate iff0
        NotF not0 -> all isObviouslyPredicate not0
        ForallF all0 -> all isObviouslyPredicate all0
        ExistsF any0 -> all isObviouslyPredicate any0
        -- Non-predicates
        _ -> False

{-|
Module      : Kore.ASTUtils.SmartConstructors
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

-- {-# OPTIONS_GHC -Wno-name-shadowing #-}

module Kore.ASTUtils.SmartConstructors
    ( -- * Utility functions for dealing with sorts
      getSort
    , forceSort
    , predicateSort
    , hasRigidHead
    , hasFlexibleHead
    , makeSortsAgree
    , ensureSortAgreement
    , isObviouslyPredicate
    -- * Lenses -- all applicative
    , patternLens
    , inputSort   -- | will have 0 or 1 inhabitants
    , resultSort  -- | will have 0 or 1 inhabitants
    , variable    -- | will have 0 or 1 inhabitants
    , allChildren -- | will have 0+ inhabitants
    , changeVar   -- | combinator for changing the `var` type in a pattern
    , inPath
    , localInPattern
    -- * Smart constructors
    , mkAnd
    , mkApp
    , mkBottom
    , mkCeil
    , mkDomainValue
    , mkEquals
    , mkExists
    , mkFloor
    , mkForall
    , mkIff
    , mkImplies
    , mkIn
    , mkNext
    , mkNot
    , mkOr
    , mkRewrites
    , mkTop
    , mkVar
    , mkStringLiteral
    , mkCharLiteral
    , mkSort
    , varS
    , symS
    ) where


import           Control.Lens hiding
                 ( (:<) )
import           Control.Monad.State
import           Data.Foldable
import           Data.Functor.Classes
                 ( Show1 )
import qualified Data.Functor.Foldable as Recursive
import           Data.Reflection
import           Data.Text
                 ( Text )

import Kore.AST.MLPatterns
import Kore.AST.Pure
import Kore.IndexedModule.MetadataTools


-- | Gets the sort of of a pattern, taking the Metadatatools implicitly
-- from the context.
-- The smart constructors `mkAnd`, etc also require this context.
-- Usage: give metadatatools (... computation with Given Metadatatools ..)
getSort
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Functor domain
        )
    => PurePattern level domain variable annotation
    -> Sort level
getSort (Recursive.project -> _ :< pat) =
    getPatternResultSort given pat

-- | Placeholder sort for when we construct a new predicate
-- But we don't know yet where it's going to be attached.
-- No particular way to avoid this, unfortunately.
-- This will probably happen often during proof routines.
predicateSort
    :: MetaOrObject level
    => Sort level
predicateSort = mkSort "PREDICATE"

patternLens
    ::  forall f level domain variable1 variable2 annotation.
        (Applicative f, MetaOrObject level, Traversable domain)
    => (Sort level -> f (Sort level))  -- ^ Operand sorts
    -> (Sort level -> f (Sort level))  -- ^ Result sorts
    -> (variable1 level -> f (variable2 level))  -- ^ Variables
    ->  (  PurePattern level domain variable1 annotation
        -> f (PurePattern level domain variable2 annotation)
        )
        -- ^ Children
    ->  (  PurePattern level domain variable1 annotation
        -> f (PurePattern level domain variable2 annotation)
        )
patternLens
    lensOperandSort   -- input sort
    lensResultSort   -- result sort
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
                DomainValuePattern <$> patternLensDomainValue dv0
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

    patternLensDomainValue
        :: level ~ Object
        => DomainValue level domain
            (PurePattern level domain variable1 annotation)
        -> f
            (DomainValue level domain
                (PurePattern level domain variable2 annotation))
    patternLensDomainValue DomainValue { domainValueSort, domainValueChild } =
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

-- | The sort of a,b in \equals(a,b), \ceil(a) etc.
inputSort
    :: (MetaOrObject level, Traversable domain)
    => Traversal' (PurePattern level domain variable annotation) (Sort level)
inputSort        f = patternLens f    pure pure pure

-- | The sort returned by a top level constructor.
-- NOTE ABOUT NOTATION:
-- In the this haskell code, this is always `s2`.
-- In the semantics.pdf documentation, the sorts are written
-- {s1} if there is one sort parameter, and {s1, s2}
-- if there are two sort parameters. This has the effect
-- that the result sort is sometimes `s1` and sometimes `s2`.
-- I always refer to the result sort as `s2`, even if
-- there is no `s1`.
-- I believe this convention is less confusing.
-- Note that a few constructors like App and StringLiteral
-- lack a result sort in the AST.
resultSort
    :: (MetaOrObject level, Traversable domain)
    => Traversal' (PurePattern level domain variable annotation) (Sort level)
resultSort = \f -> patternLens pure f pure pure

-- | Points to the bound variable in Forall/Exists,
-- and also the Variable in VariablePattern
variable
    :: (MetaOrObject level, Traversable domain)
    => Traversal'
        (PurePattern level domain variable annotation)
        (variable level)
variable = \f -> patternLens pure pure f pure

-- | All sub-expressions which are 'Pattern's.
-- Use partsOf allChildren to get a lens to a List.
allChildren
    :: (MetaOrObject level, Traversable domain)
    => Traversal'
        (PurePattern level domain variable annotation)
        (PurePattern level domain variable annotation)
allChildren = patternLens pure pure pure

changeVar
    :: (MetaOrObject level, Applicative f, Traversable domain)
    => (variable1 level -> f (variable2 level))
    ->  (  PurePattern level domain variable1 annotation
        -> f (PurePattern level domain variable2 annotation)
        )
    ->  (  PurePattern level domain variable1 annotation
        -> f (PurePattern level domain variable2 annotation)
        )
changeVar = patternLens pure pure

-- | Applies a function at an `[Int]` path.
localInPattern
    :: (MetaOrObject level, Traversable domain)
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
    :: (MetaOrObject level, Applicative f, Traversable domain)
    => [Int]
    ->  (  PurePattern level domain variable annotation
        -> f (PurePattern level domain variable annotation)
        )
    ->  (  PurePattern level domain variable annotation
        -> f (PurePattern level domain variable annotation)
        )
inPath []       = id --aka the identity lens
inPath (n : ns) = partsOf allChildren . ix n . inPath ns

-- | Rigid pattern heads are those which have a
-- single uniquely determined sort,
-- which we can't change.
hasRigidHead
    :: (MetaOrObject level, Functor domain)
    => PurePattern level domain variable annotation
    -> Bool
hasRigidHead (Recursive.project -> _ :< pat) =
    case pat of
        ApplicationPattern   _ -> True
        DomainValuePattern   _ -> True
        VariablePattern      _ -> True
        StringLiteralPattern _ -> True
        CharLiteralPattern   _ -> True
        _                      -> False

-- | Flexible pattern heads are those which can be
-- any sort, like predicates \equals, \ceil etc.
-- The 3rd possibility (not hasFlexibleHead && not hasRigidHead)
-- is a constructor whose sort
-- must match the sort of of its subexpressions:
-- \and, \or, \implies, etc.
hasFlexibleHead
    :: (MetaOrObject level, Functor domain)
    => PurePattern level domain variable annotation
    -> Bool
hasFlexibleHead (Recursive.project -> _ :< pat) =
    case pat of
        BottomPattern _ -> True
        CeilPattern   _ -> True
        EqualsPattern _ -> True
        FloorPattern  _ -> True
        InPattern     _ -> True
        TopPattern    _ -> True
        _               -> False

-- | Attempts to modify p to have sort s.
forceSort
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Traversable domain
        )
    => Sort level
    -> PurePattern level domain variable annotation
    -> Maybe (PurePattern level domain variable annotation)
forceSort s p
  | getSort p == s = Just p
  | hasRigidHead    p   = Nothing
  | hasFlexibleHead p   = Just $ p & resultSort .~ s
  | otherwise      = traverseOf allChildren (forceSort s) p

-- | Modify all patterns in a list to have the same sort.
makeSortsAgree
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Traversable domain
        )
    => [PurePattern level domain variable annotation]
    -> Maybe [PurePattern level domain variable annotation]
makeSortsAgree ps =
    forM ps $ forceSort $
        case asum $ getRigidSort <$> ps of
          Nothing -> predicateSort
          Just a  -> a

getRigidSort
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Traversable domain
        )
    => PurePattern level domain variable annotation
    -> Maybe (Sort level)
getRigidSort p =
    case forceSort predicateSort p of
      Nothing -> Just $ getSort p
      Just _  -> Nothing

-- | Ensures that the subpatterns of a pattern match in their sorts
-- and assigns the correct sort to the top level pattern
-- i.e. converts the invalid (x : Int /\ ( x < 3 : Float)) : Bool
-- to the valid (x : Int /\ (x < 3 : Int)) : Int
ensureSortAgreement
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable annotation
    -> PurePattern level domain variable annotation
ensureSortAgreement p =
  case makeSortsAgree $ p ^. partsOf allChildren of
    Just []    -> p & resultSort .~ predicateSort
    Just ps@(c : _) ->
      p & (partsOf allChildren) .~ ps
        & inputSort  .~ getSort c
        & resultSort .~ (
          if hasFlexibleHead p
            then predicateSort
            else getSort c
          )
    Nothing -> error $ "Can't unify sorts of subpatterns: " ++ show (() <$ p)

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

-- | Constructors that handle sort information automatically.
-- To use, put `give metadatatools` at the top of the computation.
mkAnd
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkAnd andFirst andSecond =
    ensureSortAgreement $ asPurePattern (mempty :< AndPattern and0)
  where
    and0 = And { andSort = fixmeSort, andFirst, andSecond }

-- TODO: Should this check for sort agreement?
mkApp
    :: (Functor domain, MetaOrObject level, Given (SymbolOrAliasSorts level))
    => SymbolOrAlias level
    -> [PurePattern level domain variable ()]
    -> PurePattern level domain variable ()
mkApp applicationSymbolOrAlias applicationChildren =
    asPurePattern (mempty :< ApplicationPattern application)
  where
    application =
        Application { applicationSymbolOrAlias, applicationChildren }

mkBottom
    :: (Functor domain, MetaOrObject level)
    => PurePattern level domain variable ()
mkBottom =
    asPurePattern (mempty :< BottomPattern bottom)
  where
    bottom = Bottom { bottomSort = predicateSort }

mkCeil
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show1 domain
        , Functor domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkCeil ceilChild =
    asPurePattern (mempty :< CeilPattern ceil)
  where
    ceil =
        Ceil
            { ceilOperandSort = getSort ceilChild
            , ceilResultSort = predicateSort
            , ceilChild
            }

mkDomainValue
    :: (Functor domain, MetaOrObject Object)
    => Sort Object
    -> domain (PurePattern Object domain variable ())
    -> PurePattern Object domain variable ()
mkDomainValue domainValueSort domainValueChild =
    asPurePattern (mempty :< DomainValuePattern domainValue)
  where
    domainValue = DomainValue { domainValueSort, domainValueChild }

mkEquals
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkEquals equalsFirst equalsSecond =
    ensureSortAgreement $ asPurePattern (mempty :< EqualsPattern equals)
  where
    equals =
        Equals
            { equalsOperandSort = fixmeSort
            , equalsResultSort = fixmeSort
            , equalsFirst
            , equalsSecond
            }

mkExists
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => variable level
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkExists existsVariable existsChild =
    ensureSortAgreement $ asPurePattern (mempty :< ExistsPattern exists)
  where
    exists = Exists { existsSort = fixmeSort, existsVariable, existsChild }

mkFloor
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (variable level)
        , Show1 domain
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkFloor floorChild =
    asPurePattern (mempty :< FloorPattern floor0)
  where
    floor0 =
        Floor
            { floorOperandSort = getSort floorChild
            , floorResultSort = predicateSort
            , floorChild
            }

mkForall
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => variable level
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkForall forallVariable forallChild =
    ensureSortAgreement $ asPurePattern (mempty :< ForallPattern forall)
  where
    forall = Forall { forallSort = fixmeSort, forallVariable, forallChild }

mkIff
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkIff iffFirst iffSecond =
    ensureSortAgreement $ asPurePattern (mempty :< IffPattern iff0)
  where
    iff0 = Iff { iffSort = fixmeSort, iffFirst, iffSecond }

mkImplies
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkImplies impliesFirst impliesSecond =
    ensureSortAgreement $ asPurePattern (mempty :< ImpliesPattern implies0)
  where
    implies0 = Implies { impliesSort = fixmeSort, impliesFirst, impliesSecond }

mkIn
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkIn inContainedChild inContainingChild =
    ensureSortAgreement $ asPurePattern (mempty :< InPattern in0)
  where
    in0 =
        In
            { inOperandSort = fixmeSort
            , inResultSort= fixmeSort
            , inContainedChild
            , inContainingChild
            }

mkNext
    ::  ( MetaOrObject Object
        , Given (SymbolOrAliasSorts Object)
        , SortedVariable variable
        , Show (PurePattern Object domain variable ())
        , Traversable domain
        )
    => PurePattern Object domain variable ()
    -> PurePattern Object domain variable ()
mkNext nextChild =
    ensureSortAgreement $ asPurePattern (mempty :< NextPattern next)
  where
    next = Next { nextSort = getSort nextChild, nextChild }

mkNot
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkNot notChild =
    ensureSortAgreement $ asPurePattern (mempty :< NotPattern not0)
  where
    not0 = Not { notSort = getSort notChild, notChild }

mkOr
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Show (PurePattern level domain variable ())
        , Traversable domain
        )
    => PurePattern level domain variable ()
    -> PurePattern level domain variable ()
    -> PurePattern level domain variable ()
mkOr orFirst orSecond =
    ensureSortAgreement $ asPurePattern (mempty :< OrPattern or0)
  where
    or0 = Or { orSort = fixmeSort, orFirst, orSecond }

mkRewrites
    ::  ( MetaOrObject Object
        , Given (SymbolOrAliasSorts Object)
        , SortedVariable var
        , Show (PurePattern Object dom var ())
        , Traversable dom
        )
    => PurePattern Object dom var ()
    -> PurePattern Object dom var ()
    -> PurePattern Object dom var ()
mkRewrites rewritesFirst rewritesSecond =
    ensureSortAgreement $ asPurePattern (mempty :< RewritesPattern rewrites0)
  where
    rewrites0 =
        Rewrites { rewritesSort = fixmeSort, rewritesFirst, rewritesSecond }

mkTop
    :: (Functor domain, MetaOrObject level)
    => PurePattern level domain variable ()
mkTop =
    asPurePattern (mempty :< TopPattern top)
  where
    top = Top { topSort = predicateSort }

mkVar
    :: (Functor domain, MetaOrObject level, Given (SymbolOrAliasSorts level))
    => variable level
    -> PurePattern level domain variable ()
mkVar var =
    asPurePattern (mempty :< VariablePattern var)

mkStringLiteral
    :: Functor domain
    => String
    -> PurePattern Meta domain variable ()
mkStringLiteral string =
    asPurePattern (mempty :< StringLiteralPattern stringLiteral)
  where
    stringLiteral = StringLiteral string

mkCharLiteral
    :: Functor domain
    => Char
    -> PurePattern Meta domain variable ()
mkCharLiteral char =
    asPurePattern (mempty :< CharLiteralPattern charLiteral)
  where
    charLiteral = CharLiteral char

mkSort
  :: MetaOrObject level
  => Text
  -> Sort level
mkSort name =
    SortActualSort $ SortActual (noLocationId name) []

-- | Construct a variable with a given name and sort
-- "x" `varS` s
varS :: MetaOrObject level => Text -> Sort level -> Variable level
varS x s =
    Variable (noLocationId x) s

-- | Construct a symbol with a given name and input sorts
-- "mult" `symS` [s, s]
-- Since the return sort is only found in MetadataTools, this is
-- mostly useful for testing.
symS :: MetaOrObject level => Text -> [Sort level] -> SymbolOrAlias level
symS x s =
    SymbolOrAlias (noLocationId x) s

-- | Placeholder. Should never appear in output of 'mk' funcs
fixmeSort
    :: MetaOrObject level
    => Sort level
fixmeSort = mkSort "FIXME"

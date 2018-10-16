{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Kore.AST.PureML
Description : Specifies the "pure" version of patterns, sentences, modules, and
              definition, which can be specialized to 'Object'-only and
              'Meta'-only objects.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.AST.PureML where

import           Data.Functor.Foldable
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Text
                 ( Text )

import Kore.AST.Common
import Kore.AST.Sentence

asPurePattern
    :: Pattern level var (PureMLPattern level var) -> PureMLPattern level var
asPurePattern = embed

fromPurePattern
    :: PureMLPattern level var -> Pattern level var (PureMLPattern level var)
fromPurePattern = project

{- | Construct a 'ConcretePurePattern' from a 'PureMLPattern'.

    A concrete pattern contains no variables, so @asConcretePurePattern@ is
    fully polymorphic on the variable type in the pure pattern. If the argument
    contains any variables, the result is @Nothing@.

 -}
asConcretePurePattern :: PureMLPattern level var -> Maybe (ConcretePurePattern level)
asConcretePurePattern =
    Functor.Foldable.fold asConcretePurePattern0
  where
    asConcretePurePattern0 pat =
        fmap Functor.Foldable.embed
            (case pat of
                AndPattern andP -> AndPattern <$> sequence andP
                ApplicationPattern appP -> ApplicationPattern <$> sequence appP
                BottomPattern botP -> BottomPattern <$> sequence botP
                CeilPattern ceilP -> CeilPattern <$> sequence ceilP
                DomainValuePattern dvP ->
                    DomainValuePattern <$> traverse sequence dvP
                EqualsPattern eqP -> EqualsPattern <$> sequence eqP
                ExistsPattern _ -> Nothing
                FloorPattern flrP -> FloorPattern <$> sequence flrP
                ForallPattern _ -> Nothing
                IffPattern iffP -> IffPattern <$> sequence iffP
                ImpliesPattern impP -> ImpliesPattern <$> sequence impP
                InPattern inP -> InPattern <$> sequence inP
                NextPattern nextP -> NextPattern <$> sequence nextP
                NotPattern notP -> NotPattern <$> sequence notP
                OrPattern orP -> OrPattern <$> sequence orP
                RewritesPattern rewP -> RewritesPattern <$> sequence rewP
                StringLiteralPattern strP -> return (StringLiteralPattern strP)
                CharLiteralPattern charP -> return (CharLiteralPattern charP)
                TopPattern topP -> TopPattern <$> sequence topP
                VariablePattern _ -> Nothing
            )

{- | Construct a 'PureMLPattern' from a 'ConcretePurePattern'.

    The concrete pattern contains no variables, so the result is fully
    polymorphic in the variable type.

 -}
fromConcretePurePattern :: ConcretePurePattern level -> PureMLPattern level var
fromConcretePurePattern =
    Functor.Foldable.fold fromConcretePurePattern0
  where
    fromConcretePurePattern0
        :: Pattern level Concrete (PureMLPattern level variable)
        -> PureMLPattern level variable
    fromConcretePurePattern0 pat =
        Functor.Foldable.embed
            (case pat of
                AndPattern andP -> AndPattern andP
                ApplicationPattern appP -> ApplicationPattern appP
                BottomPattern botP -> BottomPattern botP
                CeilPattern ceilP -> CeilPattern ceilP
                DomainValuePattern dvP -> DomainValuePattern dvP
                EqualsPattern eqP -> EqualsPattern eqP
                ExistsPattern Exists { existsVariable } ->
                    -- existsVariable has uninhabited type.
                    -- The empty case below convinces GHC that this branch is
                    -- unreachable.
                    case existsVariable of {}
                FloorPattern flrP -> FloorPattern flrP
                ForallPattern Forall { forallVariable } ->
                    -- forallVariable has uninhabited type.
                    -- The empty case below convinces GHC that this branch is
                    -- unreachable.
                    case forallVariable of {}
                IffPattern iffP -> IffPattern iffP
                ImpliesPattern impP -> ImpliesPattern impP
                InPattern inP -> InPattern inP
                NextPattern nextP -> NextPattern nextP
                NotPattern notP -> NotPattern notP
                OrPattern orP -> OrPattern orP
                RewritesPattern rewP -> RewritesPattern rewP
                StringLiteralPattern strP -> StringLiteralPattern strP
                CharLiteralPattern charP -> CharLiteralPattern charP
                TopPattern topP -> TopPattern topP
                VariablePattern varP ->
                    -- varP has uninhabited type.
                    -- The empty case below convinces GHC that this branch is
                    -- unreachable.
                    case varP of {}
            )

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom level =
    SentenceAxiom (SortVariable level) (Pattern level) Variable
-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias level =
    SentenceAlias level (Pattern level) Variable
-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol level =
    SentenceSymbol level (Pattern level) Variable
-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport level =
    SentenceImport (Pattern level) Variable

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence level =
    Sentence level (SortVariable level) (Pattern level) Variable

instance AsSentence (PureSentence level) (PureSentenceAlias level) where
    asSentence = SentenceAliasSentence

instance AsSentence (PureSentence level) (PureSentenceSymbol level) where
    asSentence = SentenceSymbolSentence

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule level =
    Module (Sentence level) (SortVariable level) (Pattern level) Variable

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition level =
    Definition
        (Sentence level) (SortVariable level) (Pattern level) Variable

-- |Given an 'Id', 'groundHead' produces the head of an 'Application'
-- corresponding to that argument.
groundHead :: Text -> AstLocation -> SymbolOrAlias level
groundHead ctor location = SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = ctor
        , idLocation = location
        }
    , symbolOrAliasParams = []
    }

-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id level -> Symbol level
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

-- |Given a head and a list of children, produces an 'ApplicationPattern'
--  applying the given head to the children
apply :: SymbolOrAlias level -> [child] -> Pattern level variable child
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

-- |Applies the given head to the empty list of children to obtain a
-- constant 'ApplicationPattern'
constant
    :: SymbolOrAlias level -> Pattern level variable child
constant patternHead = apply patternHead []

type UnFixedPureMLPattern level variable =
    Pattern level variable (PureMLPattern level variable)
type UnfixedCommonPurePattern level = UnFixedPureMLPattern level Variable

type PurePatternStub level variable =
    PatternStub level variable (PureMLPattern level variable)

type CommonPurePatternStub level =
    PurePatternStub level Variable

{-| 'mapPatternVariables' replaces all variables in a 'PureMLPattern'
using the provided mapping.
-}
mapPatternVariables
    :: (variableFrom level -> variableTo level)
    -> PureMLPattern level variableFrom
    -> PureMLPattern level variableTo
mapPatternVariables mapper = cata (Fix . mapPatternVariable mapper)

{-| 'mapPatternVariables' replaces the variables occurring directly
(i.e. without recursion) in a 'Pattern', using the provided mapping.
-}
mapPatternVariable
    :: (variableFrom level -> variableTo level)
    -> Pattern level variableFrom child
    -> Pattern level variableTo child
mapPatternVariable _ (AndPattern (And a b c)) =
    AndPattern (And a b c)
mapPatternVariable _ (ApplicationPattern (Application a b)) =
    ApplicationPattern (Application a b)
mapPatternVariable _ (BottomPattern (Bottom a)) =
    BottomPattern (Bottom a)
mapPatternVariable _ (CeilPattern (Ceil a b c)) =
    CeilPattern (Ceil a b c)
mapPatternVariable _ (DomainValuePattern (DomainValue a b)) =
    DomainValuePattern (DomainValue a b)
mapPatternVariable _ (EqualsPattern (Equals a b c d)) =
    EqualsPattern (Equals a b c d)
mapPatternVariable wrapper (ExistsPattern exists) =
    ExistsPattern exists
        { existsVariable = wrapper (existsVariable exists)
        }
mapPatternVariable _ (FloorPattern (Floor a b c)) =
    FloorPattern (Floor a b c)
mapPatternVariable wrapper (ForallPattern forall) =
    ForallPattern forall
        { forallVariable = wrapper (forallVariable forall)}
mapPatternVariable _ (IffPattern (Iff a b c)) =
    IffPattern (Iff a b c)
mapPatternVariable _ (ImpliesPattern (Implies a b c)) =
    ImpliesPattern (Implies a b c)
mapPatternVariable _ (InPattern (In a b c d)) =
    InPattern (In a b c d)
mapPatternVariable _ (NextPattern (Next a b)) =
    NextPattern (Next a b)
mapPatternVariable _ (NotPattern (Not a b)) =
    NotPattern (Not a b)
mapPatternVariable _ (OrPattern (Or a b c)) =
    OrPattern (Or a b c)
mapPatternVariable _ (RewritesPattern (Rewrites a b c)) =
    RewritesPattern (Rewrites a b c)
mapPatternVariable _ (StringLiteralPattern (StringLiteral a)) =
    StringLiteralPattern (StringLiteral a)
mapPatternVariable _ (CharLiteralPattern (CharLiteral a)) =
    CharLiteralPattern (CharLiteral a)
mapPatternVariable _ (TopPattern (Top a)) =
    TopPattern (Top a)
mapPatternVariable wrapper (VariablePattern variable) =
    VariablePattern (wrapper variable)

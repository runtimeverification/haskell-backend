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

import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Foldable
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Text
                 ( Text )
import           Data.Void
                 ( Void )

import Kore.AST.Common
import Kore.AST.MetaOrObject

asPurePattern
    :: Functor dom
    => Pattern level dom var (PureMLPattern level dom var)
    -> PureMLPattern level dom var
asPurePattern = embed

fromPurePattern
    :: Functor dom
    => PureMLPattern level dom var
    -> Pattern level dom var (PureMLPattern level dom var)
fromPurePattern = project

{- | Construct a 'ConcretePurePattern' from a 'PureMLPattern'.

    A concrete pattern contains no variables, so @asConcretePurePattern@ is
    fully polymorphic on the variable type in the pure pattern. If the argument
    contains any variables, the result is @Nothing@.

 -}
asConcretePurePattern
    ::  forall level dom var.
        Traversable dom
    => PureMLPattern level dom var
    -> Maybe (ConcretePurePattern level dom)
asConcretePurePattern =
    Functor.Foldable.fold asConcretePurePattern0
  where
    asConcretePurePattern0
        :: Pattern level dom var (Maybe (ConcretePurePattern level dom))
        -> Maybe (ConcretePurePattern level dom)
    asConcretePurePattern0 pat =
        fmap Functor.Foldable.embed
            (case pat of
                AndPattern andP -> AndPattern <$> sequence andP
                ApplicationPattern appP -> ApplicationPattern <$> sequence appP
                BottomPattern botP -> BottomPattern <$> sequence botP
                CeilPattern ceilP -> CeilPattern <$> sequence ceilP
                DomainValuePattern dvP -> DomainValuePattern <$> sequence dvP
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
fromConcretePurePattern
    ::  forall level domain variable.
        Functor domain
    => ConcretePurePattern level domain
    -> PureMLPattern level domain variable
fromConcretePurePattern =
    Functor.Foldable.fold fromConcretePurePattern0
  where
    fromConcretePurePattern0
        :: Pattern level domain Concrete (PureMLPattern level domain variable)
        -> PureMLPattern level domain variable
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
apply :: SymbolOrAlias level -> [child] -> Pattern level domain variable child
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

-- |Applies the given head to the empty list of children to obtain a
-- constant 'ApplicationPattern'
constant
    :: SymbolOrAlias level -> Pattern level domain variable child
constant patternHead = apply patternHead []

type UnFixedPureMLPattern level domain variable =
    Pattern level domain variable (PureMLPattern level domain variable)
type UnfixedCommonPurePattern level domain =
    UnFixedPureMLPattern level domain Variable

type PurePatternStub level domain variable =
    PatternStub level domain variable (PureMLPattern level domain variable)

type CommonPurePatternStub level domain =
    PurePatternStub level domain Variable

{-| 'mapPatternVariables' replaces all variables in a 'PureMLPattern'
using the provided mapping.
-}
mapPatternVariables
    :: Functor domain
    => (variableFrom level -> variableTo level)
    -> PureMLPattern level domain variableFrom
    -> PureMLPattern level domain variableTo
mapPatternVariables mapper = cata (Fix . mapPatternVariable mapper)

{-| 'mapPatternVariables' replaces the variables occurring directly
(i.e. without recursion) in a 'Pattern', using the provided mapping.
-}
mapPatternVariable
    :: (variableFrom level -> variableTo level)
    -> Pattern level domain variableFrom child
    -> Pattern level domain variableTo child
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

{- | Cast a pure pattern with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: PureMLPattern level (Const Void) variable
    -> PureMLPattern level domain variable
castVoidDomainValues = mapPatternDomainValues (\case {})

{- | Cast a pattern head with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head can be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValue
    :: Pattern level (Const Void) variable child
    -> Pattern level domain variable child
castVoidDomainValue = mapPatternDomainValue (\case {})

mapPatternDomainValues
    :: Functor domain
    => (forall child'. domain child' -> domain' child')
    -> PureMLPattern level domain variable
    -> PureMLPattern level domain' variable
mapPatternDomainValues mapping = cata (Fix . mapPatternDomainValue mapping)

mapPatternDomainValue
    :: (forall child'. domain child' -> domain' child')
    -> Pattern level domain variable child
    -> Pattern level domain' variable child
mapPatternDomainValue mapping =
    \case
        DomainValuePattern dvP ->
            DomainValuePattern dvP
                { domainValueChild = mapping domainValueChild }
          where
            DomainValue { domainValueChild } = dvP
        AndPattern andP -> AndPattern andP
        ApplicationPattern appP -> ApplicationPattern appP
        BottomPattern botP -> BottomPattern botP
        CeilPattern ceilP -> CeilPattern ceilP
        EqualsPattern eqP -> EqualsPattern eqP
        ExistsPattern existsP -> ExistsPattern existsP
        FloorPattern flrP -> FloorPattern flrP
        ForallPattern forallP -> ForallPattern forallP
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
        VariablePattern varP -> VariablePattern varP

{- | Cast a 'Meta'-pure-pattern into any domain.

The pattern can be cast trivially because it meta-patterns contain no
domain values.

 -}
castMetaDomainValues
    :: (Functor domain, Functor domain')
    => PureMLPattern Meta domain variable
    -> PureMLPattern Meta domain' variable
castMetaDomainValues = cata (Functor.Foldable.embed . castMetaDomainValue)

{- | Cast a 'Meta'-pattern head into any domain.

The pattern head can be cast trivially because it meta-patterns contain no
domain values.

 -}
castMetaDomainValue
    :: Pattern Meta domain variable child
    -> Pattern Meta domain' variable child
castMetaDomainValue =
    \case
        AndPattern andP -> AndPattern andP
        ApplicationPattern appP -> ApplicationPattern appP
        BottomPattern botP -> BottomPattern botP
        CeilPattern ceilP -> CeilPattern ceilP
        EqualsPattern eqP -> EqualsPattern eqP
        ExistsPattern existsP -> ExistsPattern existsP
        FloorPattern flrP -> FloorPattern flrP
        ForallPattern forallP -> ForallPattern forallP
        IffPattern iffP -> IffPattern iffP
        ImpliesPattern impP -> ImpliesPattern impP
        InPattern inP -> InPattern inP
        NotPattern notP -> NotPattern notP
        OrPattern orP -> OrPattern orP
        StringLiteralPattern strP -> StringLiteralPattern strP
        CharLiteralPattern charP -> CharLiteralPattern charP
        TopPattern topP -> TopPattern topP
        VariablePattern varP -> VariablePattern varP

{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.PatternF
    ( PatternF (..)
    , mapVariables
    , traverseVariables
    , mapDomainValues
    , castVoidDomainValues
    -- * Pure pattern heads
    , groundHead
    , constant
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Functor.Classes
import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
import           Data.Text
                 ( Text )
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.CharLiteral
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Next
import Kore.Syntax.Not
import Kore.Syntax.Or
import Kore.Syntax.Rewrites
import Kore.Syntax.SetVariable
import Kore.Syntax.StringLiteral
import Kore.Syntax.Top
import Kore.Unparser

{- | 'PatternF' is the 'Base' functor of Kore patterns

-}
data PatternF domain variable child
    = AndPattern           !(And Sort child)
    | ApplicationPattern   !(Application SymbolOrAlias child)
    | BottomPattern        !(Bottom Sort child)
    | CeilPattern          !(Ceil Sort child)
    | DomainValuePattern   !(domain child)
    | EqualsPattern        !(Equals Sort child)
    | ExistsPattern        !(Exists Sort variable child)
    | FloorPattern         !(Floor Sort child)
    | ForallPattern        !(Forall Sort variable child)
    | IffPattern           !(Iff Sort child)
    | ImpliesPattern       !(Implies Sort child)
    | InPattern            !(In Sort child)
    | NextPattern          !(Next Sort child)
    | NotPattern           !(Not Sort child)
    | OrPattern            !(Or Sort child)
    | RewritesPattern      !(Rewrites Sort child)
    | StringLiteralPattern !StringLiteral
    | CharLiteralPattern   !CharLiteral
    | TopPattern           !(Top Sort child)
    | VariablePattern      !variable
    | InhabitantPattern    !Sort
    | SetVariablePattern   !(SetVariable variable)
    deriving (Foldable, Functor, Generic, Traversable)

Deriving.deriveEq1 ''PatternF
Deriving.deriveOrd1 ''PatternF
Deriving.deriveShow1 ''PatternF

instance
    (Eq1 domain, Eq variable, Eq child) =>
    Eq (PatternF domain variable child)
  where
    (==) = eq1
    {-# INLINE (==) #-}

instance
    (Ord1 domain, Ord variable, Ord child) =>
    Ord (PatternF domain variable child)
  where
    compare = compare1
    {-# INLINE compare #-}

instance
    (Show1 domain, Show variable, Show child) =>
    Show (PatternF domain variable child)
  where
    showsPrec = showsPrec1
    {-# INLINE showsPrec #-}

instance
    ( Hashable child
    , Hashable variable
    , Hashable (domain child)
    ) =>
    Hashable (PatternF domain variable child)

instance
    ( NFData child
    , NFData variable
    , NFData (domain child)
    ) =>
    NFData (PatternF domain variable child)

instance
    ( Unparse child
    , Unparse (domain child)
    , Unparse variable
    ) =>
    Unparse (PatternF domain variable child)
  where
    unparse =
        \case
            AndPattern p           -> unparse p
            ApplicationPattern p   -> unparse p
            BottomPattern p        -> unparse p
            CeilPattern p          -> unparse p
            DomainValuePattern p   -> unparse p
            EqualsPattern p        -> unparse p
            ExistsPattern p        -> unparse p
            FloorPattern p         -> unparse p
            ForallPattern p        -> unparse p
            IffPattern p           -> unparse p
            ImpliesPattern p       -> unparse p
            InPattern p            -> unparse p
            NextPattern p          -> unparse p
            NotPattern p           -> unparse p
            OrPattern p            -> unparse p
            RewritesPattern p      -> unparse p
            StringLiteralPattern p -> unparse p
            CharLiteralPattern p   -> unparse p
            TopPattern p           -> unparse p
            VariablePattern p      -> unparse p
            InhabitantPattern s          -> unparse s
            SetVariablePattern p   -> unparse p

    unparse2 =
        \case
            AndPattern p           -> unparse2 p
            ApplicationPattern p   -> unparse2 p
            BottomPattern p        -> unparse2 p
            CeilPattern p          -> unparse2 p
            DomainValuePattern p   -> unparse2 p
            EqualsPattern p        -> unparse2 p
            ExistsPattern p        -> unparse2 p
            FloorPattern p         -> unparse2 p
            ForallPattern p        -> unparse2 p
            IffPattern p           -> unparse2 p
            ImpliesPattern p       -> unparse2 p
            InPattern p            -> unparse2 p
            NextPattern p          -> unparse2 p
            NotPattern p           -> unparse2 p
            OrPattern p            -> unparse2 p
            RewritesPattern p      -> unparse2 p
            StringLiteralPattern p -> unparse2 p
            CharLiteralPattern p   -> unparse2 p
            TopPattern p           -> unparse2 p
            VariablePattern p      -> unparse2 p
            InhabitantPattern s          -> unparse s
            SetVariablePattern p   -> unparse p

{- | Use the provided mapping to replace all variables in a 'PatternF' head.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

-}
mapVariables
    :: (variable1 -> variable2)
    -> PatternF domain variable1 child
    -> PatternF domain variable2 child
mapVariables mapping =
    runIdentity . traverseVariables (Identity . mapping)
{-# INLINE mapVariables #-}

{- | Use the provided traversal to replace all variables in a 'PatternF' head.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

-}
traverseVariables
    :: Applicative f
    => (variable1 -> f variable2)
    -> PatternF domain variable1 child
    -> f (PatternF domain variable2 child)
traverseVariables traversing =
    \case
        -- Non-trivial cases
        ExistsPattern any0 -> ExistsPattern <$> traverseVariablesExists any0
        ForallPattern all0 -> ForallPattern <$> traverseVariablesForall all0
        VariablePattern variable -> VariablePattern <$> traversing variable
        InhabitantPattern s -> pure (InhabitantPattern s)
        SetVariablePattern (SetVariable variable)
            -> SetVariablePattern . SetVariable <$> traversing variable
        -- Trivial cases
        AndPattern andP -> pure (AndPattern andP)
        ApplicationPattern appP -> pure (ApplicationPattern appP)
        BottomPattern botP -> pure (BottomPattern botP)
        CeilPattern ceilP -> pure (CeilPattern ceilP)
        DomainValuePattern dvP -> pure (DomainValuePattern dvP)
        EqualsPattern eqP -> pure (EqualsPattern eqP)
        FloorPattern flrP -> pure (FloorPattern flrP)
        IffPattern iffP -> pure (IffPattern iffP)
        ImpliesPattern impP -> pure (ImpliesPattern impP)
        InPattern inP -> pure (InPattern inP)
        NextPattern nxtP -> pure (NextPattern nxtP)
        NotPattern notP -> pure (NotPattern notP)
        OrPattern orP -> pure (OrPattern orP)
        RewritesPattern rewP -> pure (RewritesPattern rewP)
        StringLiteralPattern strP -> pure (StringLiteralPattern strP)
        CharLiteralPattern charP -> pure (CharLiteralPattern charP)
        TopPattern topP -> pure (TopPattern topP)
  where
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort <$> traversing existsVariable <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort <$> traversing forallVariable <*> pure forallChild

-- | Use the provided mapping to replace all domain values in a 'PatternF' head.
mapDomainValues
    :: (forall child'. domain1 child' -> domain2 child')
    -> PatternF domain1 variable child
    -> PatternF domain2 variable child
mapDomainValues mapping =
    \case
        -- Non-trivial case
        DomainValuePattern domainP -> DomainValuePattern (mapping domainP)
        InhabitantPattern s -> InhabitantPattern s
        -- Trivial cases
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
        SetVariablePattern varP -> SetVariablePattern varP

{- | Cast a 'PatternF' head with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head can be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: PatternF (Const Void) variable child
    -> PatternF domain       variable child
castVoidDomainValues = mapDomainValues (\case {})

-- | Given an 'Id', 'groundHead' produces the head of an 'Application'
-- corresponding to that argument.
groundHead :: Text -> AstLocation -> SymbolOrAlias
groundHead ctor location = SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = ctor
        , idLocation = location
        }
    , symbolOrAliasParams = []
    }

-- | Given a head and a list of children, produces an 'ApplicationPattern'
--  applying the given head to the children
apply :: SymbolOrAlias -> [child] -> PatternF domain variable child
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

-- |Applies the given head to the empty list of children to obtain a
-- constant 'ApplicationPattern'
constant :: SymbolOrAlias -> PatternF domain variable child
constant patternHead = apply patternHead []

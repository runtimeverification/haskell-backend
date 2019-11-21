{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Or
    ( simplifyEvaluated
    , simplify
    ) where

import Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike

-- * Driver

{- | 'simplify' simplifies an 'Or' pattern into an 'OrPattern'.

'simplify' is the driver responsible for breaking down an @\\or@ pattern and
merging its children.

-}
simplify
    :: InternalVariable variable
    => Or Sort (OrPattern variable)
    -> OrPattern variable
simplify Or { orFirst = first, orSecond = second } =
    simplifyEvaluated first second

{- | Simplify an 'Or' given its two 'OrPattern' children.

See also: 'simplify'

-}
simplifyEvaluated
    :: InternalVariable variable
    => OrPattern variable
    -> OrPattern variable
    -> OrPattern variable

{-

__TODO__ (virgil): Preserve pattern sorts under simplification.
One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

@
CofreeF (Or Sort) (Attribute.Pattern variable) (OrPattern variable)
@

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}

{-
__TODO__ (virgil): This should do all possible mergings, not just the first term
with the second.
-}

simplifyEvaluated first second

  | (head1 : tail1) <- MultiOr.extractPatterns first
  , (head2 : tail2) <- MultiOr.extractPatterns second
  , Just result <- simplifySinglePatterns head1 head2
  = OrPattern.fromPatterns $ result : (tail1 ++ tail2)

  | otherwise =
    MultiOr.merge first second

  where
    simplifySinglePatterns first' second' =
        topAnnihilates first' second'


-- * Top annihilates Or

{- | 'Top' patterns are the annihilator of 'Or'.

@⊤@ is the annihilator of @∨@; when two configurations have the same
substitution, it may be possible to use this property to simplify the pair by
annihilating the lesser term.

@
(⊤,              p₁, s) ∨ (t₂,              p₂, s)
(⊤, [p₂ ∨ ¬p₂] ∧ p₁, s) ∨ (t₂, [p₁ ∨ ¬p₁] ∧ p₂, s)

(⊤, p₁ ∧ p₂, s) ∨ (⊤, p₁ ∧ ¬p₂, s) ∨ (t₂, ¬p₁ ∧ p₂, s)
@

It is useful to apply the above equality when

@
¬p₂ ∧ p₁ = ¬p₁ ∧ p₂ = ⊥
p₁ = p₂
@

so that

@
(⊤, p₁, s) ∨ (t₂, p₂, s) = (⊤, p₁ ∧ p₂, s)
  where
    p₁ = p₂.
@
 -}
topAnnihilates
    :: InternalVariable variable
    => Pattern variable
    -- ^ Configuration
    -> Pattern variable
    -- ^ Disjunction
    -> Maybe (Pattern variable)
topAnnihilates
    predicated1@Conditional
        { term = term1
        , predicate = predicate1
        , substitution = substitution1
        }
    predicated2@Conditional
        { term = term2
        , predicate = predicate2
        , substitution = substitution2
        }

  -- The 'term's are checked first because checking the equality of predicates
  -- and substitutions could be expensive.

  | isTop term1
  , predicate1    == predicate2
  , substitution1 == substitution2
  = Just predicated1

  | isTop term2
  , predicate1    == predicate2
  , substitution1 == substitution2
  = Just predicated2

  | otherwise =
    Nothing

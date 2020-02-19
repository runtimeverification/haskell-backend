module Test.Kore.Step.Simplification
    ( Simplifier, Env (..)
    , runSimplifier
    , runSimplifierBranch
    , simplifiedCondition
    , simplifiedOrCondition
    , simplifiedOrPattern
    , simplifiedPattern
    , simplifiedPredicate
    , simplifiedSubstitution
    , simplifiedTerm
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import qualified Data.Functor.Foldable as Recursive

import Branch
    ( BranchT
    )
import qualified Kore.Attribute.Pattern as Attribute.Pattern
    ( fullySimplified
    , setSimplified
    )
import Kore.Internal.Condition
    ( Condition
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( splitTerm
    , withCondition
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Step.Simplification.Data
    ( Env (..)
    , Simplifier
    )
import qualified Kore.Step.Simplification.Data as Kore

import qualified Test.SMT as Test

runSimplifier :: Env Simplifier -> Simplifier a -> IO a
runSimplifier env = Test.runSMT . Kore.runSimplifier env

runSimplifierBranch :: Env Simplifier -> BranchT Simplifier a -> IO [a]
runSimplifierBranch env = Test.runSMT . Kore.runSimplifierBranch env

simplifiedTerm :: TermLike variable -> TermLike variable
simplifiedTerm =
    Recursive.unfold (simplifiedWorker . Recursive.project)
  where
    simplifiedWorker (attrs :< patt) =
        Attribute.Pattern.setSimplified Attribute.Pattern.fullySimplified attrs
        :< patt

simplifiedPredicate :: Predicate variable -> Predicate variable
simplifiedPredicate = fmap simplifiedTerm

simplifiedSubstitution
    :: InternalVariable variable
    => Substitution variable
    -> Substitution variable
simplifiedSubstitution =
    Substitution.unsafeWrap
    . fmap Substitution.assignmentToPair
    . Substitution.unwrap
    . Substitution.mapTerms simplifiedTerm

simplifiedCondition
    :: InternalVariable variable
    => Condition variable
    -> Condition variable
simplifiedCondition Conditional { term = (), predicate, substitution } =
    Conditional
        { term = ()
        , predicate = simplifiedPredicate predicate
        , substitution = simplifiedSubstitution substitution
        }

simplifiedPattern
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
simplifiedPattern patt =
    simplifiedTerm term `Pattern.withCondition` simplifiedCondition condition
  where
    (term, condition) = Pattern.splitTerm patt

simplifiedOrPattern
    :: InternalVariable variable
    => OrPattern variable
    -> OrPattern variable
simplifiedOrPattern = fmap simplifiedPattern

simplifiedOrCondition
    :: InternalVariable variable
    => OrCondition variable
    -> OrCondition variable
simplifiedOrCondition = fmap simplifiedCondition

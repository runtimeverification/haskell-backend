{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

module Kore.Step.TermLike
    ( TermLike
    , module Kore.AST.MetaOrObject
    , module Kore.AST.Pure
    , freeVariables
    , hasFreeVariable
    , withoutFreeVariable
    , mapVariables
    , traverseVariables
    , asConcreteStepPattern
    , fromConcreteStepPattern
    , substitute
    , externalizeFreshVariables
    ) where

import           Control.Comonad
import qualified Control.Lens as Lens
import           Control.Monad.Reader
                 ( Reader )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.Annotation.Valid
                 ( Valid )
import qualified Kore.Annotation.Valid as Valid
import           Kore.AST.Common
                 ( Exists (..), Forall (..), Pattern (..),
                 SortedVariable (..) )
import qualified Kore.AST.Common as Base
import           Kore.AST.MetaOrObject
import           Kore.AST.Pure
                 ( And, Application, Bottom, Ceil, CharLiteral, CofreeF (..),
                 Concrete, DomainValue, Equals, Exists, Floor, Forall, Id (..),
                 Iff, Implies, In, Next, Not, Or, PurePattern, Rewrites, Sort,
                 SortActual, SortVariable, SortedVariable, StringLiteral,
                 SymbolOrAlias (..), Top, Variable (..) )
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Substitute as Substitute
import           Kore.Unparser
import           Kore.Variables.Fresh

type TermLike variable =
    PurePattern Object Domain.Builtin variable (Valid (variable Object) Object)

freeVariables :: TermLike variable -> Set (variable Object)
freeVariables termLike = Valid.freeVariables (extract termLike)

hasFreeVariable
    :: Ord (variable Object)
    => variable Object
    -> TermLike variable
    -> Bool
hasFreeVariable variable = Set.member variable . freeVariables

{- | Throw an error if the variable occurs free in the pattern.

Otherwise, the argument is returned.

 -}
withoutFreeVariable
    ::  ( Ord (variable Object)
        , Unparse (variable Object)
        )
    => variable Object  -- ^ variable
    -> TermLike variable
    -> a  -- ^ result, if the variable does not occur free in the pattern
    -> a
withoutFreeVariable variable termLike result
  | hasFreeVariable variable termLike =
    (error . show . Pretty.vsep)
        [ Pretty.hsep
            [ "Unexpected free variable"
            , unparse variable
            , "in pattern:"
            ]
        , Pretty.indent 4 (unparse termLike)
        ]
  | otherwise = result

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord (variable2 Object)
    => (variable1 Object -> variable2 Object)
    -> TermLike variable1
    -> TermLike variable2
mapVariables mapping =
    Recursive.unfold (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (valid :< pat) =
        Valid.mapVariables mapping valid :< Base.mapVariables mapping pat

{- | Use the provided traversal to replace all variables in a 'TermLike'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord (variable2 Object))
    => (variable1 Object -> m (variable2 Object))
    -> TermLike variable1
    -> m (TermLike variable2)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker (valid :< pat) =
        Recursive.embed <$> projected
      where
        projected =
            (:<)
                <$> Valid.traverseVariables traversing valid
                <*> (Base.traverseVariables traversing =<< sequence pat)

{- | Construct a 'ConcreteStepPattern' from a 'TermLike'.

A concrete pattern contains no variables, so @asConcreteStepPattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcreteStepPattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcreteStepPattern
    :: TermLike variable
    -> Maybe (TermLike Concrete)
asConcreteStepPattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'TermLike' from a 'ConcreteStepPattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcreteStepPattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcreteStepPattern
    :: Ord (variable Object)
    => TermLike Concrete
    -> TermLike variable
fromConcreteStepPattern = mapVariables (\case {})

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
substitute
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        )
    => Map (variable level) (TermLike variable)
    -> TermLike variable
    -> TermLike variable
substitute = Substitute.substitute (Lens.lens getFreeVariables setFreeVariables)
  where
    getFreeVariables = Valid.freeVariables
    setFreeVariables valid freeVars = valid { Valid.freeVariables = freeVars }

{- | Reset the 'variableCounter' of all 'Variables'.

@externalizeFreshVariables@ resets the 'variableCounter' of all variables, while
ensuring that no 'Variable' in the result is accidentally captured.

 -}
externalizeFreshVariables
    :: forall level. MetaOrObject level
    => TermLike Variable
    -> TermLike Variable
externalizeFreshVariables termLike =
    Reader.runReader
        (Recursive.fold externalizeFreshVariablesWorker termLike)
        renamedFreeVariables
  where
    -- | 'originalFreeVariables' are present in the original pattern; they do
    -- not have a generated counter. 'generatedFreeVariables' have a generated
    -- counter, usually because they were introduced by applying some axiom.
    (originalFreeVariables, generatedFreeVariables) =
        Set.partition Base.isOriginalVariable (freeVariables termLike)

    -- | The map of generated free variables, renamed to be unique from the
    -- original free variables.
    (renamedFreeVariables, _) =
        Foldable.foldl' rename initial generatedFreeVariables
      where
        initial = (Map.empty, originalFreeVariables)
        rename (renaming, avoiding) variable =
            let
                variable' = safeVariable avoiding variable
                renaming' = Map.insert variable variable' renaming
                avoiding' = Set.insert variable' avoiding
            in
                (renaming', avoiding')

    {- | Look up a variable renaming.

    The original (not generated) variables of the pattern are never renamed, so
    these variables are not present in the Map of renamed variables.

     -}
    lookupVariable variable =
        Reader.asks (Map.lookup variable) >>= \case
            Nothing -> return variable
            Just variable' -> return variable'

    {- | Externalize a variable safely.

    The variable's counter is incremented until its externalized form is unique
    among the set of avoided variables. The externalized form is returned.

     -}
    safeVariable avoiding variable =
        head  -- 'head' is safe because 'iterate' creates an infinite list
        $ dropWhile wouldCapture
        $ Base.externalizeFreshVariable
        <$> iterate nextVariable variable
      where
        wouldCapture var = Set.member var avoiding

    underBinder freeVariables' variable child = do
        let variable' = safeVariable freeVariables' variable
        child' <- Reader.local (Map.insert variable variable') child
        return (variable', child')

    externalizeFreshVariablesWorker
        ::  Base
                (TermLike Variable)
                (Reader
                    (Map (Variable level) (Variable level))
                    (TermLike Variable)
                )
        ->  (Reader
                (Map (Variable level) (Variable level))
                (TermLike Variable)
            )
    externalizeFreshVariablesWorker (valid :< patt) = do
        valid' <- Valid.traverseVariables lookupVariable valid
        let freeVariables' = Valid.freeVariables valid'
        patt' <-
            case patt of
                ExistsPattern exists -> do
                    let Exists { existsVariable, existsChild } = exists
                    (existsVariable', existsChild') <-
                        underBinder
                            freeVariables'
                            existsVariable
                            existsChild
                    let exists' =
                            exists
                                { existsVariable = existsVariable'
                                , existsChild = existsChild'
                                }
                    return (ExistsPattern exists')
                ForallPattern forall -> do
                    let Forall { forallVariable, forallChild } = forall
                    (forallVariable', forallChild') <-
                        underBinder
                            freeVariables'
                            forallVariable
                            forallChild
                    let forall' =
                            forall
                                { forallVariable = forallVariable'
                                , forallChild = forallChild'
                                }
                    return (ForallPattern forall')
                _ ->
                    Base.traverseVariables lookupVariable patt >>= sequence
        (return . Recursive.embed) (valid' :< patt')

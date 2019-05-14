{-|
Module      : Kore.ASTVerifier.PatternVerifier
Description : Tools for verifying the wellformedness of a Kore 'Pattern'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.PatternVerifier
    ( verifyPattern
    , verifyStandalonePattern
    , verifyNoPatterns
    , verifyAliasLeftPattern
    , verifyFreeVariables
    , withDeclaredVariables
    , PatternVerifier (..)
    , runPatternVerifier
    , Context (..)
    , DeclaredVariables (..), emptyDeclaredVariables
    , assertExpectedSort
    , assertSameSort
    ) where

import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( (<+>) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc.Render.String
                 ( renderString )

import           Kore.AST.Error
import           Kore.ASTHelpers
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Internal.TermLike
                 ( Builtin, TermLike )
import qualified Kore.Internal.TermLike as Internal
import           Kore.Parser
                 ( ParsedPattern )
import           Kore.Syntax as Syntax
import           Kore.Syntax.Definition
import           Kore.Unparser
import qualified Kore.Variables.Free as Variables
import qualified Kore.Verified as Verified

newtype DeclaredVariables =
    DeclaredVariables
        { getDeclaredVariables :: Map.Map Id (Variable) }
    deriving (Monoid, Semigroup)

emptyDeclaredVariables :: DeclaredVariables
emptyDeclaredVariables = mempty

data Context =
    Context
        { declaredVariables :: !DeclaredVariables
        , declaredSortVariables :: !(Set SortVariable)
        -- ^ The sort variables in scope.
        , indexedModule :: !(IndexedModule () Attribute.Null Attribute.Null)
        -- ^ The indexed Kore module containing all definitions in scope.
        , builtinDomainValueVerifiers
            :: !(Builtin.DomainValueVerifiers Verified.Pattern)
        }

newtype PatternVerifier a =
    PatternVerifier
        { getPatternVerifier :: ReaderT Context (Either (Error VerifyError)) a }
    deriving (Applicative, Functor, Monad)

deriving instance MonadReader Context PatternVerifier

deriving instance e ~ VerifyError => MonadError (Error e) PatternVerifier

runPatternVerifier
    :: Context
    -> PatternVerifier a
    -> Either (Error VerifyError) a
runPatternVerifier ctx PatternVerifier { getPatternVerifier } =
    runReaderT getPatternVerifier ctx

lookupSortDeclaration
    :: Id
    -> PatternVerifier (SentenceSort ())
lookupSortDeclaration sortId = do
    Context { indexedModule } <- Reader.ask
    (_, sortDecl) <- resolveSort indexedModule sortId
    return sortDecl

lookupAliasDeclaration :: Id -> PatternVerifier (SentenceAlias ())
lookupAliasDeclaration aliasId = do
    Context { indexedModule } <- Reader.ask
    (_, aliasDecl) <- resolveAlias indexedModule aliasId
    return aliasDecl

lookupSymbolDeclaration :: Id -> PatternVerifier (SentenceSymbol ())
lookupSymbolDeclaration symbolId = do
    Context { indexedModule } <- Reader.ask
    (_, symbolDecl) <- resolveSymbol indexedModule symbolId
    return symbolDecl

lookupDeclaredVariable :: Id -> PatternVerifier Variable
lookupDeclaredVariable varId = do
    variables <- Reader.asks (getDeclaredVariables . declaredVariables)
    maybe errorUnquantified return $ Map.lookup varId variables
  where
    errorUnquantified :: PatternVerifier Variable
    errorUnquantified =
        koreFailWithLocations [varId]
            ("Unquantified variable: '" ++ getIdForError varId ++ "'.")

addDeclaredVariable
    :: Variable
    -> DeclaredVariables
    -> DeclaredVariables
addDeclaredVariable variable (getDeclaredVariables -> variables) =
    DeclaredVariables $ Map.insert (variableName variable) variable variables

{- | Add a new variable to the set of 'DeclaredVariables'.

The new variable must not already be declared.

 -}
newDeclaredVariable
    :: DeclaredVariables
    -> Variable
    -> PatternVerifier DeclaredVariables
newDeclaredVariable declared variable@Variable { variableName } = do
    let declaredVariables = getDeclaredVariables declared
    case Map.lookup variableName declaredVariables of
        Just variable' -> alreadyDeclared variable'
        Nothing -> return (addDeclaredVariable variable declared)
  where
    alreadyDeclared :: Variable -> PatternVerifier DeclaredVariables
    alreadyDeclared variable' =
        koreFailWithLocations [variable', variable]
            ("Variable '"
                ++ getIdForError variableName
                ++ "' was already declared."
            )

{- | Collect 'DeclaredVariables'.

Each variable in the 'Foldable' collection must be unique.

See also: 'newDeclaredVariable'

 -}
uniqueDeclaredVariables
    :: Foldable f
    => f (Variable)
    -> PatternVerifier DeclaredVariables
uniqueDeclaredVariables =
    Foldable.foldlM newDeclaredVariable emptyDeclaredVariables

{- | Run a 'PatternVerifier' in a particular variable context.

See also: 'verifyStandalonePattern'

 -}
withDeclaredVariables
    :: DeclaredVariables
    -> PatternVerifier a
    -> PatternVerifier a
withDeclaredVariables declaredVariables' =
    Reader.local (\ctx -> ctx { declaredVariables = declaredVariables' })

{- | Verify the left-hand side of an alias definition.

The left-hand side must consist of the alias applied to a non-repeating sequence
of variables with the same sorts as the alias declaration.

The verified left-hand side is returned with the set of 'DeclaredVariables'. The
'DeclaredVariables' are used to verify the right-hand side of the alias
definition.

See also: 'uniqueDeclaredVariables', 'withDeclaredVariables'

 -}
verifyAliasLeftPattern
    :: Application SymbolOrAlias (Variable)
    -> PatternVerifier
        (DeclaredVariables, Application SymbolOrAlias (Variable))
verifyAliasLeftPattern leftPattern = do
    _ :< verified <- verifyApplication snd (expectVariable <$> leftPattern)
    declaredVariables <- uniqueDeclaredVariables (fst <$> verified)
    let verifiedLeftPattern = fst <$> verified
    return (declaredVariables, verifiedLeftPattern)
  where
    expectVariable
        :: Variable
        -> PatternVerifier (Variable, Attribute.Pattern Variable)
    expectVariable var = do
        verifyVariableDeclaration var
        let
            patternSort = variableSort var
            freeVariables = Set.singleton var
            valid = Attribute.Pattern { patternSort, freeVariables }
        return (var, valid)

{- | Verify that a Kore pattern is well-formed.

This includes verifying that:
- the pattern has the expected sort (if provided)
- the sorts of all subterms agree
- all variables are explicitly quantified

 -}
verifyPattern
    :: Maybe Sort
    -- ^ If present, represents the expected sort of the pattern.
    -> ParsedPattern
    -> PatternVerifier Verified.Pattern
verifyPattern expectedSort korePattern = do
    verified <- Recursive.fold verifyPatternWorker korePattern
    assertExpectedSort expectedSort (Internal.extractAttributes verified)
    return verified
  where
    verifyPatternWorker base = Recursive.embed <$> verifyObjectPattern base

{- | Verify a Kore pattern with implicitly-quantified variables.

@verifyStandalonePattern@ calls 'verifyPattern', but quantifies all free
variables of the pattern.

See also: 'verifyPattern', 'verifyFreeVariables', 'withDeclaredVariables'

 -}
verifyStandalonePattern
    :: Maybe Sort
    -> ParsedPattern
    -> PatternVerifier Verified.Pattern
verifyStandalonePattern expectedSort korePattern = do
    declaredVariables <- verifyFreeVariables korePattern
    withDeclaredVariables declaredVariables
        (verifyPattern expectedSort korePattern)

{- | Fail if a Kore pattern is found.

@verifyNoPatterns@ is useful to 'traverse' sentence types with phantom pattern
type variables.

 -}
verifyNoPatterns
    :: MonadError (Error VerifyError) m
    => ParsedPattern
    -> m Verified.Pattern
verifyNoPatterns _ = koreFail "Unexpected pattern."

verifyObjectPattern
    :: Base ParsedPattern (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Base (TermLike Variable) Verified.Pattern)
verifyObjectPattern base@(_ :< patternF) =
    withLocationAndContext patternF patternName $ verifyPatternHead base
  where
    patternName = patternNameForContext patternF

verifyPatternHead
    :: Base ParsedPattern (PatternVerifier Verified.Pattern)
    -> PatternVerifier (Base (TermLike Variable) Verified.Pattern)
verifyPatternHead (_ :< patternF) =
    case patternF of
        Syntax.AndF and' ->
            transCofreeF Internal.AndF <$> verifyAnd and'
        Syntax.ApplicationF app ->
            transCofreeF Internal.ApplicationF
            <$> verifyApplication Internal.extractAttributes app
        Syntax.BottomF bottom ->
            transCofreeF Internal.BottomF <$> verifyBottom bottom
        Syntax.CeilF ceil' ->
            transCofreeF Internal.CeilF <$> verifyCeil ceil'
        Syntax.DomainValueF dv ->
            transCofreeF Internal.BuiltinF <$> verifyDomainValue dv
        Syntax.EqualsF equals' ->
            transCofreeF Internal.EqualsF <$> verifyEquals equals'
        Syntax.ExistsF exists ->
            transCofreeF Internal.ExistsF <$> verifyExists exists
        Syntax.FloorF floor' ->
            transCofreeF Internal.FloorF <$> verifyFloor floor'
        Syntax.ForallF forall' ->
            transCofreeF Internal.ForallF <$> verifyForall forall'
        Syntax.IffF iff ->
            transCofreeF Internal.IffF <$> verifyIff iff
        Syntax.ImpliesF implies ->
            transCofreeF Internal.ImpliesF <$> verifyImplies implies
        Syntax.InF in' ->
            transCofreeF Internal.InF <$> verifyIn in'
        Syntax.NextF next ->
            transCofreeF Internal.NextF <$> verifyNext next
        Syntax.NotF not' ->
            transCofreeF Internal.NotF <$> verifyNot not'
        Syntax.OrF or' ->
            transCofreeF Internal.OrF <$> verifyOr or'
        Syntax.RewritesF rewrites ->
            transCofreeF Internal.RewritesF <$> verifyRewrites rewrites
        Syntax.StringLiteralF str ->
            transCofreeF (Internal.StringLiteralF . getConst)
                <$> verifyStringLiteral str
        Syntax.CharLiteralF char ->
            transCofreeF (Internal.CharLiteralF . getConst)
                <$> verifyCharLiteral char
        Syntax.TopF top ->
            transCofreeF Internal.TopF <$> verifyTop top
        Syntax.VariableF var ->
            transCofreeF (Internal.VariableF . getConst)
                <$> verifyVariable var
        Syntax.InhabitantF _ ->
            koreFail "Unexpected pattern."
        Syntax.SetVariableF (SetVariable var) ->
            transCofreeF (Internal.SetVariableF . SetVariable . getConst)
                <$> verifyVariable var
  where
    transCofreeF fg (a :< fb) = a :< fg fb

verifyPatternSort :: Sort -> PatternVerifier ()
verifyPatternSort patternSort = do
    Context { declaredSortVariables } <- Reader.ask
    _ <- verifySort lookupSortDeclaration declaredSortVariables patternSort
    return ()

verifyOperands
    :: Traversable operator
    => (forall a. operator a -> Sort)
    -> operator (PatternVerifier Verified.Pattern)
    ->  PatternVerifier
            (CofreeF operator (Attribute.Pattern Variable) Verified.Pattern)
verifyOperands operandSort = \operator -> do
    let patternSort = operandSort operator
        expectedSort = Just patternSort
    verifyPatternSort patternSort
    let verifyChildWithSort verify = do
            child <- verify
            assertExpectedSort expectedSort (Internal.extractAttributes child)
            return child
    verified <- traverse verifyChildWithSort operator
    let freeVariables =
            Foldable.foldl' Set.union Set.empty
                (Internal.freeVariables <$> verified)
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)
{-# INLINE verifyOperands #-}

verifyAnd
    ::  ( logical ~ And Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyAnd = verifyOperands andSort

verifyOr
    ::  ( logical ~ Or Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyOr = verifyOperands orSort

verifyIff
    ::  ( logical ~ Iff Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyIff = verifyOperands iffSort

verifyImplies
    ::  ( logical ~ Implies Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyImplies = verifyOperands impliesSort

verifyBottom
    ::  ( logical ~ Bottom Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyBottom = verifyOperands bottomSort

verifyTop
    ::  ( logical ~ Top Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyTop = verifyOperands topSort

verifyNot
    ::  ( logical ~ Not Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyNot = verifyOperands notSort

verifyRewrites
    ::  ( logical ~ Rewrites Sort
        , valid ~ Attribute.Pattern Variable
        )
    => logical (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF logical valid Verified.Pattern)
verifyRewrites = verifyOperands rewritesSort

verifyPredicate
    ::  ( Traversable predicate
        , valid ~ Attribute.Pattern Variable
        )
    => (forall a. predicate a -> Sort)  -- ^ Operand sort
    -> (forall a. predicate a -> Sort)  -- ^ Result sort
    -> predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyPredicate operandSort resultSort = \predicate -> do
    let patternSort = resultSort predicate
    verifyPatternSort patternSort
    Attribute.Pattern { freeVariables } :< verified <-
        verifyOperands operandSort predicate
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)
{-# INLINE verifyPredicate #-}

verifyCeil
    ::  ( predicate ~ Ceil Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyCeil = verifyPredicate ceilOperandSort ceilResultSort

verifyFloor
    ::  ( predicate ~ Floor Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyFloor = verifyPredicate floorOperandSort floorResultSort

verifyEquals
    ::  ( predicate ~ Equals Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyEquals = verifyPredicate equalsOperandSort equalsResultSort

verifyIn
    ::  ( predicate ~ In Sort
        , valid ~ Attribute.Pattern Variable
        )
    => predicate (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF predicate valid Verified.Pattern)
verifyIn = verifyPredicate inOperandSort inResultSort

verifyNext
    ::  ( operator ~ Next Sort
        , valid ~ Attribute.Pattern Variable
        )
    => operator (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF operator valid Verified.Pattern)
verifyNext = verifyOperands nextSort

verifyPatternsWithSorts
    :: (child -> Attribute.Pattern Variable)
    -> [Sort]
    -> [PatternVerifier child]
    -> PatternVerifier [child]
verifyPatternsWithSorts getChildAttributes sorts operands = do
    koreFailWhen (declaredOperandCount /= actualOperandCount)
        (  "Expected "
        ++ show declaredOperandCount
        ++ " operands, but got "
        ++ show actualOperandCount
        ++ "."
        )
    Monad.zipWithM
        (\sort verify -> do
            verified <- verify
            assertExpectedSort (Just sort) (getChildAttributes verified)
            return verified
        )
        sorts
        operands
  where
    declaredOperandCount = length sorts
    actualOperandCount = length operands

verifyApplication
    ::  (child -> Attribute.Pattern Variable)
    ->  Application SymbolOrAlias (PatternVerifier child)
    ->  PatternVerifier
            (CofreeF
                (Application SymbolOrAlias)
                (Attribute.Pattern Variable)
                child
            )
verifyApplication getChildAttributes application = do
    applicationSorts <- verifySymbolOrAlias applicationSymbolOrAlias
    let ApplicationSorts { applicationSortsOperands } = applicationSorts
        operandSorts = applicationSortsOperands
    verifiedChildren <- verifyChildren operandSorts applicationChildren
    let patternSort = applicationSortsResult applicationSorts
        verified = application { applicationChildren = verifiedChildren }
        freeVariables =
            Set.unions (getChildFreeVariables <$> verifiedChildren)
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)
  where
    verifyChildren = verifyPatternsWithSorts getChildAttributes
    getChildFreeVariables = Attribute.freeVariables . getChildAttributes
    Application { applicationSymbolOrAlias } = application
    Application { applicationChildren } = application

verifyBinder
    ::  ( Traversable binder
        , valid ~ Attribute.Pattern Variable
        )
    => (forall a. binder a -> Sort)
    -> (forall a. binder a -> Variable)
    -> binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyBinder binderSort binderVariable = \binder -> do
    let variable = binderVariable binder
        patternSort = binderSort binder
    verifyVariableDeclaration variable
    verifyPatternSort patternSort
    let withQuantifiedVariable ctx@Context { declaredVariables } =
            ctx
                { declaredVariables =
                    addDeclaredVariable
                        variable
                        declaredVariables
                }
    valid :< binder' <-
        Reader.local
            withQuantifiedVariable
            (verifyOperands binderSort binder)
    let valid' = Attribute.deleteFreeVariable variable valid
    return (valid' :< binder')
{-# INLINE verifyBinder #-}

verifyExists
    ::  ( binder ~ Exists Sort Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyExists = verifyBinder existsSort existsVariable

verifyForall
    ::  ( binder ~ Forall Sort Variable
        , valid ~ Attribute.Pattern Variable
        )
    => binder (PatternVerifier Verified.Pattern)
    -> PatternVerifier (CofreeF binder valid Verified.Pattern)
verifyForall = verifyBinder forallSort forallVariable

verifyVariable
    ::  ( base ~ Const (Variable)
        , valid ~ Attribute.Pattern Variable
        )
    => Variable
    -> PatternVerifier (CofreeF base valid Verified.Pattern)
verifyVariable variable@Variable { variableName, variableSort } = do
    declaredVariable <- lookupDeclaredVariable variableName
    let Variable { variableSort = declaredSort } = declaredVariable
    koreFailWithLocationsWhen
        (variableSort /= declaredSort)
        [ variable, declaredVariable ]
        "The declared sort is different."
    let patternSort = variableSort
        verified = Const variable
        freeVariables = Set.singleton variable
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)

verifyDomainValue
    :: Domain.External (PatternVerifier Verified.Pattern)
    ->   PatternVerifier
            (CofreeF Builtin (Attribute.Pattern Variable) Verified.Pattern)
verifyDomainValue domain = do
    let DomainValue { domainValueSort = patternSort } =
            Lens.view Domain.lensDomainValue domain
    Context { builtinDomainValueVerifiers, indexedModule } <- Reader.ask
    verifyPatternSort patternSort
    let lookupSortDeclaration' sortId = do
            (_, sortDecl) <- resolveSort indexedModule sortId
            return sortDecl
    domain' <- sequence domain
    verified <-
        PatternVerifier
        $ Reader.lift
        $ Builtin.verifyDomainValue
            builtinDomainValueVerifiers
            lookupSortDeclaration'
            domain'
    let freeVariables =
            Foldable.foldl' Set.union Set.empty
                (Attribute.freeVariables . Internal.extractAttributes <$> verified)
    Monad.unless (Set.null freeVariables)
        (koreFail "Domain value must not contain free variables.")
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)

verifyStringLiteral
    :: (base ~ Const StringLiteral, valid ~ Attribute.Pattern variable)
    => StringLiteral
    -> PatternVerifier (CofreeF base valid Verified.Pattern)
verifyStringLiteral str = do
    let patternSort = stringMetaSort
        freeVariables = Set.empty
        verified = Const str
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)

verifyCharLiteral
    :: (base ~ Const CharLiteral, valid ~ Attribute.Pattern variable)
    => CharLiteral
    -> PatternVerifier (CofreeF base valid Verified.Pattern)
verifyCharLiteral char = do
    let patternSort = charMetaSort
        freeVariables = Set.empty
        verified = Const char
    return (Attribute.Pattern { patternSort, freeVariables } :< verified)

verifyVariableDeclaration :: Variable -> PatternVerifier VerifySuccess
verifyVariableDeclaration Variable { variableSort } = do
    Context { declaredSortVariables } <- Reader.ask
    verifySort
        lookupSortDeclaration
        declaredSortVariables
        variableSort

verifySymbolOrAlias
    :: SymbolOrAlias
    -> PatternVerifier ApplicationSorts
verifySymbolOrAlias symbolOrAlias = do
    trySymbol <- catchError (Right <$> lookupSymbol) (return . Left)
    tryAlias <- catchError (Right <$> lookupAlias) (return . Left)
    case (trySymbol, tryAlias) of
        (Right sentenceSymbol, Left _) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceSymbol
        (Left _, Right sentenceAlias) ->
            applicationSortsFromSymbolOrAliasSentence
                symbolOrAlias
                sentenceAlias
        (Left err, Left _) -> throwError err
        (Right _, Right _) -> error
            (  "The (Right, Right) match should be caught "
            ++ "by the unique names check."
            )
  where
    lookupSymbol = lookupSymbolDeclaration applicationId
    lookupAlias = lookupAliasDeclaration applicationId
    applicationId = symbolOrAliasConstructor symbolOrAlias

applicationSortsFromSymbolOrAliasSentence
    :: SentenceSymbolOrAlias sentence
    => SymbolOrAlias
    -> sentence pat
    -> PatternVerifier ApplicationSorts
applicationSortsFromSymbolOrAliasSentence symbolOrAlias sentence = do
    Context { declaredSortVariables } <- Reader.ask
    mapM_
        ( verifySort
            lookupSortDeclaration
            declaredSortVariables
        )
        (symbolOrAliasParams symbolOrAlias)
    symbolOrAliasSorts (symbolOrAliasParams symbolOrAlias) sentence

assertSameSort
    :: Sort
    -> Sort
    -> PatternVerifier ()
assertSameSort expectedSort actualSort = do
    koreFailWithLocationsWhen
        (expectedSort /= actualSort)
        [expectedSort, actualSort]
        ((renderString . Pretty.layoutCompact)
         ("Expecting sort"
          <+> Pretty.squotes (unparse expectedSort)
          <+> "but got"
          <+> Pretty.squotes (unparse actualSort)
          <> Pretty.dot)
        )

assertExpectedSort
    :: Maybe Sort
    -> Attribute.Pattern variable
    -> PatternVerifier ()
assertExpectedSort Nothing _ = return ()
assertExpectedSort (Just expected) Attribute.Pattern { patternSort } =
    assertSameSort expected patternSort

verifyFreeVariables
    :: ParsedPattern
    -> PatternVerifier DeclaredVariables
verifyFreeVariables unifiedPattern =
    Monad.foldM
        addFreeVariable
        emptyDeclaredVariables
        (Set.toList (Variables.freePureVariables unifiedPattern))

addFreeVariable
    :: DeclaredVariables
    -> Variable
    -> PatternVerifier DeclaredVariables
addFreeVariable (getDeclaredVariables -> vars) var = do
    checkVariable var vars
    return $ DeclaredVariables $ Map.insert (variableName var) var vars

checkVariable
    :: Variable
    -> Map.Map Id Variable
    -> PatternVerifier VerifySuccess
checkVariable var vars =
    maybe verifySuccess inconsistent $ Map.lookup (variableName var) vars
  where
    inconsistent v =
        koreFailWithLocations [v, var]
        $ renderString $ Pretty.layoutCompact
        $ "Inconsistent free variable usage:"
            <+> unparse v
            <+> "and"
            <+> unparse var
            <> Pretty.dot

patternNameForContext :: PatternF dom Variable p -> String
patternNameForContext (AndF _) = "\\and"
patternNameForContext (ApplicationF application) =
    "symbol or alias '"
    ++ getIdForError
        (symbolOrAliasConstructor (applicationSymbolOrAlias application))
    ++ "'"
patternNameForContext (BottomF _) = "\\bottom"
patternNameForContext (CeilF _) = "\\ceil"
patternNameForContext (DomainValueF _) = "\\dv"
patternNameForContext (EqualsF _) = "\\equals"
patternNameForContext (ExistsF exists) =
    "\\exists '"
    ++ variableNameForContext (existsVariable exists)
    ++ "'"
patternNameForContext (FloorF _) = "\\floor"
patternNameForContext (ForallF forall) =
    "\\forall '"
    ++ variableNameForContext (forallVariable forall)
    ++ "'"
patternNameForContext (IffF _) = "\\iff"
patternNameForContext (ImpliesF _) = "\\implies"
patternNameForContext (InF _) = "\\in"
patternNameForContext (NextF _) = "\\next"
patternNameForContext (NotF _) = "\\not"
patternNameForContext (OrF _) = "\\or"
patternNameForContext (RewritesF _) = "\\rewrites"
patternNameForContext (StringLiteralF _) = "<string>"
patternNameForContext (CharLiteralF _) = "<char>"
patternNameForContext (TopF _) = "\\top"
patternNameForContext (VariableF variable) =
    "variable '" ++ variableNameForContext variable ++ "'"
patternNameForContext (InhabitantF _) = "\\inh"
patternNameForContext (SetVariableF (SetVariable variable)) =
    "set variable '" ++ variableNameForContext variable ++ "'"

variableNameForContext :: Variable -> String
variableNameForContext variable = getIdForError (variableName variable)

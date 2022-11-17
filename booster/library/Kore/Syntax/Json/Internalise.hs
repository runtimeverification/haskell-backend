{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Syntax.Json.Internalise (
    internalisePattern,
    internaliseTermOrPredicate,
    internaliseTerm,
    internalisePredicate,
    PatternError (..),
    checkSort,
    matchSorts,
    SortError (..),
) where

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Extra
import Control.Monad.Trans.Except
import Data.Aeson (ToJSON (..), Value, object, (.=))
import Data.Bifunctor
import Data.Foldable ()
import Data.List (foldl1', nub)
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text, intercalate, pack)

import Kore.Definition.Attributes.Base
import Kore.Definition.Base (KoreDefinition (..), SymbolSort (..))
import Kore.Pattern.Base qualified as Internal
import Kore.Pattern.Util (sortOfTerm)
import Kore.Syntax.Json.Base qualified as Syntax
import Kore.Syntax.Json.Externalise (externaliseSort)

internalisePattern ::
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Pattern
internalisePattern sortVars definition p = do
    (terms, predicates) <- partitionM isTermM $ explodeAnd p

    when (null terms) $ throwE $ NoTermFound p

    -- construct an AndTerm from all terms (checking sort consistency)
    term <- andTerm p =<< mapM (internaliseTerm sortVars definition) terms
    -- internalise all predicates
    constraints <- mapM (internalisePredicate sortVars definition) predicates
    pure Internal.Pattern{term, constraints}
  where
    andTerm :: Syntax.KorePattern -> [Internal.Term] -> Except PatternError Internal.Term
    andTerm _ [] = error "BUG: andTerm called with empty term list"
    andTerm pat ts = do
        let sortList = nub $ map sortOfTerm ts
            andSort = head sortList
            resultTerm = foldl1' (Internal.AndTerm andSort) ts
        -- check resulting terms for consistency and sorts
        -- TODO needs to consider sub-sorts instead (set must be
        -- consistent) if this code becomes order-sorted
        unless (length sortList == 1) $
            throwE $
                PatternSortError pat (IncompatibleSorts $ map externaliseSort sortList)
        pure resultTerm

internaliseTermOrPredicate ::
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except [PatternError] Internal.TermOrPredicate
internaliseTermOrPredicate sortVars definition syntaxPatt =
    Internal.APredicate <$> (withExcept (: []) $ internalisePredicate sortVars definition syntaxPatt)
        <|> Internal.TermAndPredicate
            <$> (withExcept (: []) $ internalisePattern sortVars definition syntaxPatt)

internaliseSort ::
    Maybe [Syntax.Id] ->
    Map Internal.SortName (SortAttributes, Set Internal.SortName) ->
    Syntax.KorePattern ->
    Syntax.Sort ->
    Except PatternError Internal.Sort
internaliseSort sortVars sorts pat =
    let knownVarSet = maybe Set.empty (Set.fromList . map Syntax.getId) sortVars
     in mapExcept (first $ PatternSortError pat) . checkSort knownVarSet sorts

-- Throws errors when a predicate is encountered. The 'And' case
-- should be analysed before, this function produces an 'AndTerm'.
internaliseTerm ::
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Term
internaliseTerm sortVars definition@KoreDefinition{sorts, symbols} pat =
    case pat of
        Syntax.KJEVar{name, sort} -> do
            variableSort <- internaliseSort' sort
            let variableName = Syntax.getId name
            pure $ Internal.Var Internal.Variable{variableSort, variableName}
        Syntax.KJSVar{name, sort} -> do
            variableSort <- internaliseSort' sort
            let variableName = Syntax.getId name
            pure $ Internal.Var Internal.Variable{variableSort, variableName}
        symPatt@Syntax.KJApp{name, sorts = appSorts, args} -> do
            (_, SymbolSort{resultSort, argSorts}) <-
                maybe (throwE $ UnknownSymbol name symPatt) pure $
                    Map.lookup (Syntax.getId name) symbols
            internalAppSorts <- mapM internaliseSort' appSorts
            -- check that all argument sorts "agree". Variables
            -- can stand for anything but need to be consistent (a
            -- matching problem returning a substitution)
            sortSubst <-
                mapExcept (first $ PatternSortError pat) $
                    foldM (uncurry . matchSorts') Map.empty $
                        zip argSorts internalAppSorts
            -- finalSort is the symbol result sort with
            -- variables substituted using the arg.sort match
            let finalSort = applySubst sortSubst resultSort
            Internal.SymbolApplication finalSort internalAppSorts (Syntax.getId name)
                <$> mapM recursion args
        Syntax.KJString{value} ->
            pure $ Internal.DomainValue (Internal.SortApp "SortString" []) value
        Syntax.KJTop{} -> predicate
        Syntax.KJBottom{} -> predicate
        Syntax.KJNot{} -> predicate
        Syntax.KJAnd{sort, first = arg1, second = arg2} -> do
            -- analysed beforehand, expecting this to operate on terms
            a <- recursion arg1
            b <- recursion arg2
            resultSort <- internaliseSort' sort
            -- TODO check that both a and b are of sort "resultSort"
            -- Which is a unification problem if this involves variables.
            pure $ Internal.AndTerm resultSort a b
        Syntax.KJOr{} -> predicate
        Syntax.KJImplies{} -> predicate
        Syntax.KJIff{} -> predicate
        Syntax.KJForall{} -> predicate
        Syntax.KJExists{} -> predicate
        Syntax.KJMu{} -> predicate
        Syntax.KJNu{} -> predicate
        Syntax.KJCeil{} -> predicate
        Syntax.KJFloor{} -> predicate
        Syntax.KJEquals{} -> predicate
        Syntax.KJIn{} -> predicate
        Syntax.KJNext{} -> predicate
        Syntax.KJRewrites{} -> predicate
        Syntax.KJDV{sort, value} ->
            Internal.DomainValue
                <$> internaliseSort' sort
                <*> pure value
        Syntax.KJMultiOr{} -> predicate
        Syntax.KJMultiApp{assoc, symbol, sorts = argSorts, argss} ->
            recursion $ withAssoc assoc (mkF symbol argSorts) argss
  where
    predicate = throwE $ TermExpected pat

    internaliseSort' = internaliseSort sortVars sorts pat

    recursion = internaliseTerm sortVars definition

-- Throws errors when a term is encountered. The 'And' case
-- is analysed before, this function produces an 'AndPredicate'.
internalisePredicate ::
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Predicate
internalisePredicate sortVars definition@KoreDefinition{sorts} pat = case pat of
    Syntax.KJEVar{} -> term
    Syntax.KJSVar{} -> term
    Syntax.KJApp{} -> term
    Syntax.KJString{} -> term
    Syntax.KJTop{} -> do
        pure Internal.Top
    Syntax.KJBottom{} -> do
        pure Internal.Bottom
    Syntax.KJNot{arg} -> do
        Internal.Not <$> recursion arg
    Syntax.KJAnd{first = arg1, second = arg2} -> do
        -- consistency should have been checked beforehand,
        -- building an AndPredicate
        Internal.AndPredicate
            <$> recursion arg1
            <*> recursion arg2
    Syntax.KJOr{first = arg1, second = arg2} ->
        Internal.Or
            <$> recursion arg1
            <*> recursion arg2
    Syntax.KJImplies{first = arg1, second = arg2} ->
        Internal.Implies
            <$> recursion arg1
            <*> recursion arg2
    Syntax.KJIff{first = arg1, second = arg2} ->
        Internal.Iff
            <$> recursion arg1
            <*> recursion arg2
    Syntax.KJForall{var, arg} ->
        Internal.Forall (Syntax.getId var) <$> recursion arg
    Syntax.KJExists{var, arg} ->
        Internal.Exists (Syntax.getId var) <$> recursion arg
    Syntax.KJMu{} -> notSupported
    Syntax.KJNu{} -> notSupported
    Syntax.KJCeil{arg} ->
        Internal.Ceil <$> internaliseTerm sortVars definition arg
    Syntax.KJFloor{} -> notSupported
    Syntax.KJEquals{sort, argSort, first = arg1, second = arg2} -> do
        -- distinguish term and predicate equality
        is1Term <- isTermM arg1
        is2Term <- isTermM arg2
        case (is1Term, is2Term) of
            (True, True) -> do
                a <- internaliseTerm sortVars definition arg1
                b <- internaliseTerm sortVars definition arg2
                s <- internaliseSort' sort
                argS <- internaliseSort' argSort
                -- check that argS and sorts of a and b "agree"
                mapM_ sortCheck [(sortOfTerm a, argS), (sortOfTerm b, argS)]
                pure $ Internal.EqualsTerm s a b
            (False, False) ->
                Internal.EqualsPredicate
                    <$> recursion arg1
                    <*> recursion arg2
            _other ->
                throwE $ InconsistentPattern pat
    Syntax.KJIn{sort, first = arg1, second = arg2} -> do
        a <- internaliseTerm sortVars definition arg1
        b <- internaliseTerm sortVars definition arg2
        s <- internaliseSort' sort
        -- TODO check that s and sorts of a and b agree
        pure $ Internal.In s a b
    Syntax.KJNext{} -> notSupported
    Syntax.KJRewrites{} -> notSupported -- should only occur in claims!
    Syntax.KJDV{} -> term
    Syntax.KJMultiOr{assoc, sort, argss} ->
        recursion $ withAssoc assoc (Syntax.KJOr sort) argss
    Syntax.KJMultiApp{} -> term
  where
    term = throwE $ PredicateExpected pat
    notSupported = throwE $ NotSupported pat

    recursion = internalisePredicate sortVars definition

    internaliseSort' = internaliseSort sortVars sorts pat

    -- check that two sorts "agree". Incomplete, see comment on ensureSortsAgree.
    sortCheck :: (Internal.Sort, Internal.Sort) -> Except PatternError ()
    sortCheck = mapExcept (first $ PatternSortError pat) . uncurry ensureSortsAgree

-- converts MultiApp and MultiOr to a chain at syntax level
withAssoc :: Syntax.LeftRight -> (a -> a -> a) -> NonEmpty a -> a
withAssoc Syntax.Left = foldl1
withAssoc Syntax.Right = foldr1

-- for use with withAssoc
mkF ::
    Syntax.Id ->
    [Syntax.Sort] ->
    Syntax.KorePattern ->
    Syntax.KorePattern ->
    Syntax.KorePattern
mkF symbol argSorts a b = Syntax.KJApp symbol argSorts [a, b]

----------------------------------------

{- | Given a set of sort variable names and a sort attribute map, checks
   a given syntactic @Sort@ and converts to an internal Sort
-}
checkSort ::
    Set Text ->
    Map Internal.SortName (SortAttributes, Set Internal.SortName) ->
    Syntax.Sort ->
    Except SortError Internal.Sort
checkSort knownVars sortMap = check'
  where
    check' :: Syntax.Sort -> Except SortError Internal.Sort
    check' var@Syntax.SortVar{name = Syntax.Id n} = do
        unless (n `Set.member` knownVars) $
            throwE (UnknownSort var)
        pure $ Internal.SortVar n
    check' app@Syntax.SortApp{name = Syntax.Id n, args} =
        do
            maybe
                (throwE $ UnknownSort app)
                ( \(SortAttributes{argCount}, _) ->
                    unless (length args == argCount) $
                        throwE (WrongSortArgCount app argCount)
                )
                (Map.lookup n sortMap)
            internalArgs <- mapM check' args
            pure $ Internal.SortApp n internalArgs

isTermM :: Syntax.KorePattern -> Except PatternError Bool
isTermM pat = case pat of
    Syntax.KJEVar{} -> pure True
    Syntax.KJSVar{} -> pure True
    Syntax.KJApp{} -> pure True
    Syntax.KJString{} -> pure True
    Syntax.KJTop{} -> pure False
    Syntax.KJBottom{} -> pure False
    Syntax.KJNot{} -> pure False
    Syntax.KJAnd{first = arg1, second = arg2} -> do
        a1Term <- isTermM arg1
        a2Term <- isTermM arg2
        when (a1Term /= a2Term) $ throwE (InconsistentPattern pat)
        pure a1Term
    Syntax.KJOr{} -> pure False
    Syntax.KJImplies{} -> pure False
    Syntax.KJIff{} -> pure False
    Syntax.KJForall{} -> pure False
    Syntax.KJExists{} -> pure False
    Syntax.KJMu{} -> notSupported
    Syntax.KJNu{} -> notSupported
    Syntax.KJCeil{} -> pure False
    Syntax.KJFloor{} -> pure False
    Syntax.KJEquals{} -> pure False
    Syntax.KJIn{} -> pure False
    Syntax.KJNext{} -> notSupported
    Syntax.KJRewrites{} -> notSupported -- should only occur in claims
    Syntax.KJDV{} -> pure True
    Syntax.KJMultiOr{} -> pure False
    Syntax.KJMultiApp{} -> pure True
  where
    notSupported = throwE $ NotSupported pat

{- | unpacks the top level of 'And' nodes of a 'KorePattern', returning
   the arguments as a list. The top-level sorts of the 'And' nodes are
   ignored, no checks are performed.
-}
explodeAnd :: Syntax.KorePattern -> [Syntax.KorePattern]
explodeAnd Syntax.KJAnd{first = arg1, second = arg2} =
    explodeAnd arg1 <> explodeAnd arg2
explodeAnd other = [other]

----------------------------------------
--- TODO find a better home for these ones. All relating to sort
--- checks, which we might not want to do too much of OTOH.

{- | Tries to find a substitution of sort variables in the given sort
 pattern (with variables) to match the given subject
-}
matchSorts ::
    -- | Pattern (contains variables to substitute)
    Internal.Sort ->
    -- | Subject (variables here are treated as constants)
    Internal.Sort ->
    Except SortError (Map Internal.VarName Internal.Sort)
matchSorts = matchSorts' Map.empty

{- | Internal matching function starting with a given substitution.
 Tries to find a substitution of sort variables in the given sort
 pattern (with variables) to match the given subject
-}
matchSorts' ::
    -- | starting substitution (accumulated)
    Map Internal.VarName Internal.Sort ->
    -- | Pattern (contains variables to substitute)
    Internal.Sort ->
    -- | Subject (variables here are treated as constants)
    Internal.Sort ->
    Except SortError (Map Internal.VarName Internal.Sort)
matchSorts' subst _pat _subj = do
    pure subst -- FIXME! traverse pattern and subject, consider given starting substitution

{- | Replace occurrences of the map key variable names in the given
 sort by their mapped sorts. There are no local binders so the
 replacement is a straightforward traversal.
-}
applySubst :: Map Internal.VarName Internal.Sort -> Internal.Sort -> Internal.Sort
applySubst subst var@(Internal.SortVar n) =
    fromMaybe var $ Map.lookup n subst
applySubst subst (Internal.SortApp n args) =
    Internal.SortApp n $ map (applySubst subst) args

{- | check that two (internal) sorts are compatible.

 For a sort application, ensure the sort constructor is the same,
 then check recursively that the arguments are compatible, too.

 Shows that the whole approach taken in this module is horribly
 incomplete wrt. sort variables (we need to propagate assumed sort
 variable bindings from the bottom up the AST to decide this.
-}
ensureSortsAgree ::
    Internal.Sort ->
    Internal.Sort ->
    Except SortError ()
ensureSortsAgree (Internal.SortVar n) _ =
    throwE $ GeneralError ("ensureSortsAgree found variable " <> n)
ensureSortsAgree _ (Internal.SortVar n) =
    throwE $ GeneralError ("ensureSortsAgree found variable " <> n)
ensureSortsAgree
    s1@(Internal.SortApp name1 args1)
    s2@(Internal.SortApp name2 args2) = do
        unless (name1 == name2) $ throwE $ IncompatibleSorts (map externaliseSort [s1, s2])
        mapM_ (uncurry ensureSortsAgree) $ zip args1 args2

----------------------------------------
data PatternError
    = NotSupported Syntax.KorePattern
    | NoTermFound Syntax.KorePattern
    | PatternSortError Syntax.KorePattern SortError
    | InconsistentPattern Syntax.KorePattern
    | TermExpected Syntax.KorePattern
    | PredicateExpected Syntax.KorePattern
    | UnknownSymbol Syntax.Id Syntax.KorePattern
    deriving stock (Eq, Show)

{- | ToJson instance (user-facing):

Renders an error string as 'error' and providing the pattern or Id in
a 'context' list.

The JSON-RPC server's error responses contain both of these fields in
a 'data' object.

If the error is a sort error, the message will contain its information
while the context provides the pattern where the error occurred.
-}
instance ToJSON PatternError where
    toJSON = \case
        NotSupported p ->
            wrap "Pattern not supported" p
        NoTermFound p ->
            wrap "Pattern must contain at least one term" p
        PatternSortError p sortErr ->
            wrap (renderSortError sortErr) p
        InconsistentPattern p ->
            wrap "Inconsistent pattern" p
        TermExpected p ->
            wrap "Expected a term but found a predicate" p
        PredicateExpected p ->
            wrap "Expected a predicate but found a term" p
        UnknownSymbol sym p ->
            wrap ("Unknown symbol " <> Syntax.getId sym) p
      where
        wrap :: Text -> Syntax.KorePattern -> Value
        wrap msg p = object ["error" .= msg, "context" .= toJSON [p]]

data SortError
    = UnknownSort Syntax.Sort
    | WrongSortArgCount Syntax.Sort Int
    | IncompatibleSorts [Syntax.Sort]
    | GeneralError Text
    deriving stock (Eq, Show)

renderSortError :: SortError -> Text
renderSortError = \case
    UnknownSort sort ->
        "Unknown " <> render sort
    WrongSortArgCount sort expected ->
        "Wrong argument count: expected "
            <> pack (show expected)
            <> " in "
            <> render sort
    IncompatibleSorts sorts ->
        "Incompatible sorts: " <> intercalate ", " (map render sorts)
    GeneralError msg ->
        msg
  where
    render = \case
        Syntax.SortVar (Syntax.Id n) ->
            "sort variable " <> n
        Syntax.SortApp (Syntax.Id n) args ->
            "sort " <> n <> "(" <> intercalate ", " (map render args) <> ")"

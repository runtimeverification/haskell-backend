{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Syntax.Json.Internalise (
    internalisePattern,
    internaliseTermOrPredicate,
    internaliseTerm,
    internalisePredicate,
    lookupInternalSort,
    PatternError (..),
    internaliseSort,
    SortError (..),
    renderSortError,
    ----------------
    explodeAnd,
    isTermM,
    textToBS,
    trm,
    handleBS,
    pattern IsQQ,
    pattern IsNotQQ,
    pattern AllowAlias,
    pattern DisallowAlias,
    pattern CheckSubsorts,
    pattern IgnoreSubsorts,
) where

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Extra
import Control.Monad.Trans.Except
import Data.Aeson (ToJSON (..), Value, object, (.=))
import Data.Bifunctor
import Data.ByteString.Char8 (ByteString, isPrefixOf)
import Data.ByteString.Char8 qualified as BS
import Data.Char (isLower)
import Data.Coerce (coerce)
import Data.Foldable ()
import Data.Generics (extQ)
import Data.List (foldl1', nub)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text as Text (Text, intercalate, pack, unpack)
import Data.Text.Encoding (decodeLatin1)
import Language.Haskell.TH (ExpQ, Lit (..), appE, litE, mkName, varE)
import Language.Haskell.TH.Quote
import Prettyprinter (pretty)

import Booster.Definition.Attributes.Base
import Booster.Definition.Attributes.Base qualified as Internal
import Booster.Definition.Base (KoreDefinition (..), emptyKoreDefinition)
import Booster.Pattern.Base (InternalisedPredicate (..))
import Booster.Pattern.Base qualified as Internal
import Booster.Pattern.Util (partitionInternalised, sortOfTerm)
import Booster.Prettyprinter (renderDefault)
import Booster.Syntax.Json.Externalise (externaliseSort)
import Booster.Syntax.ParsedKore.Parser (parsePattern)
import Kore.Syntax.Json.Types qualified as Syntax

pattern IsQQ, IsNotQQ :: Flag "qq"
pattern IsQQ = Flag True
pattern IsNotQQ = Flag False

{-# COMPLETE IsQQ, IsNotQQ #-}

pattern AllowAlias, DisallowAlias :: Flag "alias"
pattern AllowAlias = Flag True
pattern DisallowAlias = Flag False

{-# COMPLETE AllowAlias, DisallowAlias #-}

pattern CheckSubsorts, IgnoreSubsorts :: Flag "subsorts"
pattern CheckSubsorts = Flag True
pattern IgnoreSubsorts = Flag False

{-# COMPLETE CheckSubsorts, IgnoreSubsorts #-}

internalisePattern ::
    Flag "alias" ->
    Flag "subsorts" ->
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError (Internal.Pattern, Map Internal.Variable Internal.Term)
internalisePattern allowAlias checkSubsorts sortVars definition p = do
    (terms, predicates) <- partitionM isTermM $ explodeAnd p

    when (null terms) $ throwE $ NoTermFound p

    -- construct an AndTerm from all terms (checking sort consistency)
    term <- andTerm p =<< mapM (internaliseTerm allowAlias checkSubsorts sortVars definition) terms
    -- internalise all predicates
    (constraints, ceilConditions, substitutions) <-
        partitionInternalised
            <$> mapM (internalisePredicate allowAlias checkSubsorts sortVars definition) predicates
    pure (Internal.Pattern{term, constraints, ceilConditions}, substitutions)
  where
    andTerm :: Syntax.KorePattern -> [Internal.Term] -> Except PatternError Internal.Term
    andTerm _ [] = error "BUG: andTerm called with empty term list"
    andTerm pat ts = do
        let sortList = nub $ map sortOfTerm ts
            resultTerm = foldl1' Internal.AndTerm ts
        -- check resulting terms for consistency and sorts
        -- TODO needs to consider sub-sorts instead (set must be
        -- consistent) if this code becomes order-sorted
        unless (length sortList == 1) $
            throwE $
                PatternSortError pat (IncompatibleSorts $ map externaliseSort sortList)
        pure resultTerm

internaliseTermOrPredicate ::
    Flag "alias" ->
    Flag "subsorts" ->
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except [PatternError] Internal.TermOrPredicates
internaliseTermOrPredicate allowAlias checkSubsorts sortVars definition syntaxPatt =
    ( withExcept (: []) $ do
        (constraints, ceilConditions, substitutions) <-
            partitionInternalised
                <$> mapM (internalisePredicate allowAlias checkSubsorts sortVars definition) (explodeAnd syntaxPatt)
        pure $ Internal.BoolOrCeilOrSubstitutionPredicates constraints ceilConditions substitutions
    )
        <|> uncurry Internal.TermAndPredicateAndSubstitution
            <$> (withExcept (: []) $ internalisePattern allowAlias checkSubsorts sortVars definition syntaxPatt)

lookupInternalSort ::
    Maybe [Syntax.Id] ->
    Map Internal.SortName (SortAttributes, Set Internal.SortName) ->
    Syntax.KorePattern ->
    Syntax.Sort ->
    Except PatternError Internal.Sort
lookupInternalSort sortVars sorts pat =
    let knownVarSet = maybe Set.empty (Set.fromList . map Syntax.getId) sortVars
     in mapExcept (first $ PatternSortError pat) . internaliseSort knownVarSet sorts

-- Throws errors when a predicate is encountered. The 'And' case
-- should be analysed before, this function produces an 'AndTerm'.
internaliseTermRaw ::
    Flag "qq" ->
    Flag "alias" ->
    Flag "subsorts" ->
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Term
internaliseTermRaw qq allowAlias checkSubsorts sortVars definition@KoreDefinition{sorts, symbols} pat =
    case pat of
        Syntax.KJEVar{name, sort} -> do
            variableSort <- lookupInternalSort' sort
            let variableName = textToBS name.getId
            pure $ Internal.Var Internal.Variable{variableSort, variableName}
        Syntax.KJSVar{name, sort} -> do
            variableSort <- lookupInternalSort' sort
            let variableName = textToBS name.getId
            pure $ Internal.Var Internal.Variable{variableSort, variableName}
        Syntax.KJApp{name, sorts = [from, to], args = [arg]}
            | Just Internal.injectionSymbol == Map.lookup (textToBS name.getId) symbols -> do
                from' <- lookupInternalSort' from
                to' <- lookupInternalSort' to
                arg' <- recursion arg
                unless (not (coerce checkSubsorts) || from' `isSubsort` to') $
                    throwE $
                        PatternSortError pat $
                            NotSubsort from' to'
                pure $ Internal.Injection from' to' arg'
        symPatt@Syntax.KJApp{name, sorts = appSorts, args} -> do
            symbol <-
                if coerce qq
                    then
                        pure $
                            Internal.Symbol
                                (textToBS name.getId)
                                []
                                []
                                (Internal.SortApp "QQ" [])
                                Internal.SymbolAttributes
                                    { symbolType = Internal.Constructor
                                    , isIdem = Internal.IsNotIdem
                                    , isAssoc = Internal.IsNotAssoc
                                    , isMacroOrAlias = Internal.IsNotMacroOrAlias
                                    , hasEvaluators = Flag False
                                    , collectionMetadata = Nothing
                                    }
                    else
                        maybe (throwE $ UnknownSymbol name symPatt) pure $
                            Map.lookup (textToBS name.getId) symbols
            -- Internalise sort variable instantiation (appSorts)
            -- Length must match sort variables in symbol declaration.
            unless (coerce qq || length appSorts == length symbol.sortVars) $
                throwE $
                    PatternSortError pat $
                        GeneralError
                            "wrong sort argument count for symbol"
            when (not (coerce allowAlias) && coerce symbol.attributes.isMacroOrAlias) $
                throwE $
                    MacroOrAliasSymbolNotAllowed name symPatt
            Internal.SymbolApplication symbol
                <$> mapM lookupInternalSort' appSorts
                <*> mapM recursion args
        Syntax.KJString{value} ->
            pure $ Internal.DomainValue (Internal.SortApp "SortString" []) $ textToBS value
        Syntax.KJTop{} -> predicate
        Syntax.KJBottom{} -> predicate
        Syntax.KJNot{} -> predicate
        Syntax.KJAnd{patterns} -> do
            -- analysed beforehand, expecting this to operate on terms
            args <- mapM recursion patterns
            -- TODO check that both a and b are of sort "resultSort"
            -- Which is a unification problem if this involves variables.
            pure $ foldr1 Internal.AndTerm args
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
                <$> lookupInternalSort' sort
                <*> pure (textToBS value)
        Syntax.KJMultiOr{} -> predicate
        Syntax.KJLeftAssoc{symbol, sorts = argSorts, argss} ->
            recursion $ foldl1 (mkF symbol argSorts) argss
        Syntax.KJRightAssoc{symbol, sorts = argSorts, argss} ->
            recursion $ foldr1 (mkF symbol argSorts) argss
  where
    predicate = throwE $ TermExpected pat

    lookupInternalSort' sort =
        if coerce qq
            then pure $ case sort of
                Syntax.SortApp{name = Syntax.Id n} -> Internal.SortApp (textToBS n) []
                Syntax.SortVar{name = Syntax.Id n} -> Internal.SortVar $ textToBS n
            else lookupInternalSort sortVars sorts pat sort

    s `isSubsort` t = case (s, t) of
        (Internal.SortApp ns _, Internal.SortApp nt _) ->
            case Map.lookup nt sorts of
                Just (_, subs) -> ns `Set.member` subs
                -- this case should be unreachable since we have already internalised these sorts and therefore know they exist
                Nothing -> False
        _ -> False

    recursion = internaliseTermRaw qq allowAlias checkSubsorts sortVars definition

internaliseTerm ::
    Flag "alias" ->
    Flag "subsorts" ->
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError Internal.Term
internaliseTerm = internaliseTermRaw IsNotQQ

-- Throws errors when a term is encountered. The 'And' case
-- is analysed before, this function produces an 'AndPredicate'.
internalisePredicate ::
    Flag "alias" ->
    Flag "subsorts" ->
    Maybe [Syntax.Id] ->
    KoreDefinition ->
    Syntax.KorePattern ->
    Except PatternError InternalisedPredicate
internalisePredicate allowAlias checkSubsorts sortVars definition@KoreDefinition{sorts} pat = case pat of
    Syntax.KJEVar{} -> term
    Syntax.KJSVar{} -> term
    Syntax.KJApp{} -> term
    Syntax.KJString{} -> term
    Syntax.KJTop{} -> pure $ IsPredicate $ Internal.Predicate Internal.TrueBool
    Syntax.KJBottom{} -> notSupported -- TODO should we throw here?
    Syntax.KJNot{arg} -> do
        recursion arg >>= \case
            IsPredicate (Internal.Predicate (Internal.EqualsInt a b)) -> pure $ IsPredicate $ Internal.Predicate $ Internal.NEqualsInt a b
            IsPredicate (Internal.Predicate (Internal.EqualsK a b)) -> pure $ IsPredicate $ Internal.Predicate $ Internal.NEqualsK a b
            IsPredicate (Internal.Predicate p) -> pure $ IsPredicate $ Internal.Predicate $ Internal.NotBool p
            IsSubstitution k v ->
                if "@" `isPrefixOf` k.variableName
                    then notSupported -- @ variables are set variables, the negation of which we do not support internalising
                    else case sortOfTerm v of
                        Internal.SortInt -> pure $ IsPredicate $ Internal.Predicate $ Internal.NEqualsInt (Internal.Var k) v
                        otherSort ->
                            pure $
                                IsPredicate $
                                    Internal.Predicate $
                                        Internal.NEqualsK (Internal.KSeq otherSort $ Internal.Var k) (Internal.KSeq otherSort v)
            _ -> notSupported
    Syntax.KJAnd{} -> notSupported
    Syntax.KJOr{} -> notSupported
    Syntax.KJImplies{} -> notSupported
    Syntax.KJIff{} -> notSupported
    Syntax.KJForall{} -> notSupported
    Syntax.KJExists{} -> notSupported
    Syntax.KJMu{} -> notSupported
    Syntax.KJNu{} -> notSupported
    Syntax.KJCeil{arg} ->
        IsCeil . Internal.Ceil <$> internaliseTerm allowAlias checkSubsorts sortVars definition arg
    Syntax.KJFloor{} -> notSupported
    Syntax.KJEquals{argSort, first = arg1, second = arg2} -> do
        -- distinguish term and predicate equality
        is1Term <- isTermM arg1
        is2Term <- isTermM arg2
        case (is1Term, is2Term) of
            (True, True) -> do
                a <- internaliseTerm allowAlias checkSubsorts sortVars definition arg1
                b <- internaliseTerm allowAlias checkSubsorts sortVars definition arg2
                argS <- lookupInternalSort' argSort
                -- check that argS and sorts of a and b "agree"
                ensureEqualSorts (sortOfTerm a) argS
                ensureEqualSorts (sortOfTerm b) argS
                case (argS, a, b) of
                    (Internal.SortBool, Internal.TrueBool, x) -> pure $ IsPredicate $ Internal.Predicate x
                    (Internal.SortBool, x, Internal.TrueBool) -> pure $ IsPredicate $ Internal.Predicate x
                    (Internal.SortBool, Internal.FalseBool, x) -> pure $ IsPredicate $ Internal.Predicate $ Internal.NotBool x
                    (Internal.SortBool, x, Internal.FalseBool) -> pure $ IsPredicate $ Internal.Predicate $ Internal.NotBool x
                    (_, Internal.Var x, t) -> pure $ IsSubstitution x t
                    (_, t, Internal.Var x) -> pure $ IsSubstitution x t
                    (Internal.SortInt, _, _) -> pure $ IsPredicate $ Internal.Predicate $ Internal.EqualsInt a b
                    (otherSort, _, _) ->
                        pure $
                            IsPredicate $
                                Internal.Predicate $
                                    Internal.EqualsK (Internal.KSeq otherSort a) (Internal.KSeq otherSort b)
            (False, False) -> notSupported
            _other ->
                throwE $ InconsistentPattern pat
    Syntax.KJIn{} -> notSupported
    Syntax.KJNext{} -> notSupported
    Syntax.KJRewrites{} -> notSupported -- should only occur in claims!
    Syntax.KJDV{} -> term
    Syntax.KJMultiOr{} -> notSupported
    Syntax.KJLeftAssoc{} -> term
    Syntax.KJRightAssoc{} -> term
  where
    term = throwE $ PredicateExpected pat
    notSupported = throwE $ NotSupported pat

    recursion = internalisePredicate allowAlias checkSubsorts sortVars definition

    lookupInternalSort' = lookupInternalSort sortVars sorts pat

    -- Recursively check that two (internal) sorts are the same.
    -- Sort variables must be eliminated (instantiated) before checking.
    ensureEqualSorts :: Internal.Sort -> Internal.Sort -> Except PatternError ()
    ensureEqualSorts s s' = mapExcept (first $ PatternSortError pat) $ go s s'
      where
        go :: Internal.Sort -> Internal.Sort -> Except SortError ()
        go s1 s2 =
            case (s1, s2) of
                (Internal.SortVar n, _) ->
                    throwE $ GeneralError ("ensureSortsAgree found variable " <> decodeLatin1 n)
                (_, Internal.SortVar n) ->
                    throwE $ GeneralError ("ensureSortsAgree found variable " <> decodeLatin1 n)
                (Internal.SortApp name1 args1, Internal.SortApp name2 args2) -> do
                    unless (name1 == name2) $
                        throwE (IncompatibleSorts (map externaliseSort [s1, s2]))
                    zipWithM_ go args1 args2

----------------------------------------

-- for use with withAssoc
mkF ::
    Syntax.Id ->
    [Syntax.Sort] ->
    Syntax.KorePattern ->
    Syntax.KorePattern ->
    Syntax.KorePattern
mkF symbol argSorts a b = Syntax.KJApp symbol argSorts [a, b]

-- primitive solution ignoring text encoding
textToBS :: Text -> ByteString
textToBS = BS.pack . Text.unpack

----------------------------------------

{- | Given a set of sort variable names and a sort attribute map, checks
   a given syntactic @Sort@ and converts to an internal Sort
-}
internaliseSort ::
    Set Text ->
    Map Internal.SortName (SortAttributes, Set Internal.SortName) ->
    Syntax.Sort ->
    Except SortError Internal.Sort
internaliseSort knownVars sortMap = check'
  where
    check' :: Syntax.Sort -> Except SortError Internal.Sort
    check' var@Syntax.SortVar{name = Syntax.Id n} = do
        unless (n `Set.member` knownVars) $
            throwE (UnknownSort var)
        pure $ Internal.SortVar $ textToBS n
    check' app@Syntax.SortApp{name = Syntax.Id n, args} =
        do
            let name = textToBS n
            maybe
                (throwE $ UnknownSort app)
                ( \(SortAttributes{argCount}, _) ->
                    unless (length args == argCount) $
                        throwE (WrongSortArgCount app argCount)
                )
                (Map.lookup name sortMap)
            internalArgs <- mapM check' args
            pure $ Internal.SortApp name internalArgs

isTermM :: Syntax.KorePattern -> Except PatternError Bool
isTermM pat = case pat of
    Syntax.KJEVar{} -> pure True
    Syntax.KJSVar{} -> pure True
    Syntax.KJApp{} -> pure True
    Syntax.KJString{} -> pure True
    Syntax.KJTop{} -> pure False
    Syntax.KJBottom{} -> pure False
    Syntax.KJNot{} -> pure False
    Syntax.KJAnd{patterns} -> do
        terms <- mapM isTermM patterns
        when (length (nub terms) /= 1) $ throwE (InconsistentPattern pat)
        pure $ head terms
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
    Syntax.KJLeftAssoc{} -> pure True
    Syntax.KJRightAssoc{} -> pure True
  where
    notSupported = throwE $ NotSupported pat

{- | unpacks the top level of 'And' nodes of a 'KorePattern', returning
   the arguments as a list. The top-level sorts of the 'And' nodes are
   ignored, no checks are performed.
-}
explodeAnd :: Syntax.KorePattern -> [Syntax.KorePattern]
explodeAnd Syntax.KJAnd{patterns} =
    concatMap explodeAnd patterns
explodeAnd other = [other]

----------------------------------------

data PatternError
    = NotSupported Syntax.KorePattern
    | NoTermFound Syntax.KorePattern
    | PatternSortError Syntax.KorePattern SortError
    | InconsistentPattern Syntax.KorePattern
    | TermExpected Syntax.KorePattern
    | PredicateExpected Syntax.KorePattern
    | UnknownSymbol Syntax.Id Syntax.KorePattern
    | MacroOrAliasSymbolNotAllowed Syntax.Id Syntax.KorePattern
    | SubstitutionNotAllowed
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
            wrap ("Unknown symbol '" <> Syntax.getId sym <> "'") p
        MacroOrAliasSymbolNotAllowed sym p ->
            wrap ("Symbol '" <> Syntax.getId sym <> "' is a macro/alias") p
        SubstitutionNotAllowed -> "Substitution predicates are not allowed here"
      where
        wrap :: Text -> Syntax.KorePattern -> Value
        wrap msg p = object ["error" .= msg, "context" .= toJSON [p]]

data SortError
    = UnknownSort Syntax.Sort
    | WrongSortArgCount Syntax.Sort Int
    | IncompatibleSorts [Syntax.Sort]
    | NotSubsort Internal.Sort Internal.Sort
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
    NotSubsort source target ->
        prettyText source <> " is not a subsort of " <> prettyText target
    GeneralError msg ->
        msg
  where
    prettyText = pack . renderDefault . pretty

    render = \case
        Syntax.SortVar (Syntax.Id n) ->
            "sort variable " <> n
        Syntax.SortApp (Syntax.Id n) args ->
            "sort " <> n <> "(" <> intercalate ", " (map render args) <> ")"

recomputeTermAttributes :: Internal.Term -> Internal.Term
recomputeTermAttributes = \case
    Internal.AndTerm t1 t2 -> Internal.AndTerm (recomputeTermAttributes t1) (recomputeTermAttributes t2)
    Internal.SymbolApplication sym sorts args -> Internal.SymbolApplication sym sorts $ map recomputeTermAttributes args
    Internal.DomainValue sort dv -> Internal.DomainValue sort dv
    Internal.Var v -> Internal.Var v
    Internal.Injection from to t -> Internal.Injection from to $ recomputeTermAttributes t
    Internal.KMap def keyVals rest ->
        Internal.KMap
            def
            (map (bimap recomputeTermAttributes recomputeTermAttributes) keyVals)
            (fmap recomputeTermAttributes rest)
    Internal.KList def heads rest ->
        Internal.KList
            def
            (map recomputeTermAttributes heads)
            (fmap (bimap recomputeTermAttributes (map recomputeTermAttributes)) rest)
    Internal.KSet def heads rest ->
        Internal.KSet
            def
            (map recomputeTermAttributes heads)
            (fmap recomputeTermAttributes rest)

trm :: QuasiQuoter
trm =
    QuasiQuoter
        { quoteExp = do
            res <-
                dataToExpQ (const Nothing `extQ` handleBS `extQ` metaSymb `extQ` metaTerm)
                    . either (error . show) id
                    . runExcept
                    . internaliseTermRaw
                        IsQQ
                        DisallowAlias
                        IgnoreSubsorts
                        Nothing
                        (emptyKoreDefinition DefinitionAttributes{})
                    . either error id
                    . parsePattern "INLINE"
                    . pack
            pure [|recomputeTermAttributes $(res)|]
        , quotePat = undefined
        , quoteType = undefined
        , quoteDec = undefined
        }
  where
    metaSymb :: Internal.Symbol -> Maybe ExpQ
    metaSymb (Internal.Symbol{name}) =
        Just [|$(varE (mkName $ BS.unpack name))|]

    metaTerm :: Internal.Term -> Maybe ExpQ
    metaTerm (Internal.Var Internal.Variable{variableName})
        | not (BS.null variableName) && isLower (BS.head variableName) =
            Just [|$(varE (mkName $ BS.unpack variableName))|]
    metaTerm _ = Nothing

handleBS :: ByteString -> Maybe ExpQ
handleBS x =
    -- convert the byte string to a string literal
    -- and wrap it back with BS.pack
    Just $ appE (varE 'BS.pack) $ litE $ StringL $ BS.unpack x

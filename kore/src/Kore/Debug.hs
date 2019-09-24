{-# OPTIONS_GHC -Wno-unused-top-binds    #-}

{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

When you have a function whose result is in a monad which is handled by
the functions below, e.g.

> f :: a -> b -> ExceptT c m d
> f arg1 arg2 = do
>     ⟨f function body⟩

then you can wrap it like this, getting information about its arguments and
result:

> f :: a -> b -> ExceptT c m d
> f arg1 arg2 =
>     traceExceptT
>         "stepWithRule"
>         ("arg1=" ++ show arg1 ++ ",arg2=" ++ show arg2)
>     $ do
>         ⟨actual f function body⟩

The output will look something like:

> starting stepWithRule with arg1=...,arg2=...
> ⟨extra tracing done by the action⟩
> ending stepWithRule with result: ...

In order to make the output readable, you can filter it through debugFilter.py,
which will indent the text and may simplify it, e.g.

> cd src/main/k/working/tests/collections/set-unify-framing-variable
> make test-k 2>&1 | python ../src/main/python/debugFilter.py > debug.txt

It also works for test error messages:

> stack -j3 test --pedantic --test-arguments --pattern=zzz 2>&1 | \
>    python ../python/debugFilter.py

Enjoy.
-}

module Kore.Debug
    (
    -- * Tracing
      traceEither
    , traceExceptT
    , traceMaybe
    , traceMaybeT
    , traceMaybeTS
    , traceNonErrorMonad
    , traceFunction
    , applyWhen
    , debugArg
    , DebugPlace (..)
    , DebugResult (..)
    -- * Debug
    , Debug (..)
    , debugPrecGeneric
    -- * Diff
    , Diff (..)
    , diffPrecEq
    , diffPrecGeneric
    ) where

import Control.Comonad.Trans.Cofree
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import Data.Functor.Const
    ( Const
    )
import Data.Functor.Identity
    ( Identity
    )
import Data.List
    ( intercalate
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    , isJust
    )
import Data.Proxy
import Data.Sequence
    ( Seq
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    , (<+>)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Void
    ( Void
    )
import Debug.Trace
import Generics.SOP
    ( All
    , All2
    , Code
    , ConstructorInfo
    , DatatypeInfo (..)
    , FieldInfo (..)
    , Generic
    , HasDatatypeInfo
    , I (..)
    , K (..)
    , NP (..)
    , NS (..)
    , SOP (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Stack as GHC
import Numeric.Natural
    ( Natural
    )

import Data.Sup
import SMT.AST
    ( SExpr
    )

{-| Identifiers for places where we're doing debug.

The intent id to use D_Generic for places where we're adding temporary debug
statements and the others for permanent debug statements
-}
data DebugPlace
    = D_Generic !String !DebugResult
    | D_OnePath_Step_transitionRule
    | D_OnePath_verifyClaim
    | D_Step
    | D_Function_evaluatePattern
    | D_SMT_refutePredicate
    | D_SMT_command
    | D_SMT_referenceCheckSort
    | D_SMT_referenceCheckSymbol
    | D_SMT_resolveSort
    | D_SMT_resolveSymbol
  deriving (Eq, Ord, Show)

data DebugArg = DebugArg { name :: !String, value :: !String }

instance Show DebugArg where
    show DebugArg {name, value} = name ++ "=" ++ show value

{-| Whether to dispay the function/action result when the function ends.
-}
data DebugResult = DebugResult | DebugNoResult
  deriving (Eq, Ord, Show)

{-| Wraps a field in order to be displayed when debugging -}
debugArg :: Show a => String -> a -> DebugArg
debugArg n v = DebugArg {name = n, value = show v}

{-|Applies a function only when the condition is met.  Useful for conditional
debugging, among other things.
-}
applyWhen :: Bool -> (a -> a) -> (a -> a)
applyWhen b f = if b then f else id

{-| Maps debug places to their debug settings.

If a place other than `D_Generic` is missing from this map, we will not log
debugging information for that place.

Example:

enabledPlaces = onePathWithFunctionNames

-}
enabledPlaces :: Map DebugPlace DebugResult
enabledPlaces = Map.empty

smt :: Map DebugPlace DebugResult
smt =
    id
    $ Map.insert D_SMT_command DebugResult
    Map.empty

smtStartup :: Map DebugPlace DebugResult
smtStartup =
    id
    $ Map.insert D_SMT_referenceCheckSort DebugResult
    $ Map.insert D_SMT_referenceCheckSymbol DebugResult
    $ Map.insert D_SMT_resolveSort DebugResult
    $ Map.insert D_SMT_resolveSymbol DebugResult
    Map.empty

onePathWithFunctionNames :: Map DebugPlace DebugResult
onePathWithFunctionNames =
    id
    $ Map.insert D_Function_evaluatePattern DebugNoResult
    $ Map.insert D_OnePath_verifyClaim DebugNoResult
    $ Map.insert D_OnePath_Step_transitionRule DebugResult
    $ Map.insert D_SMT_refutePredicate DebugResult
      Map.empty

executionWithFunctionNames :: Map DebugPlace DebugResult
executionWithFunctionNames =
    id
    $ Map.insert D_Function_evaluatePattern DebugNoResult
    $ Map.insert D_Step DebugNoResult
      Map.empty

traceWhenEnabled
    :: DebugPlace -> (DebugResult -> a -> a) -> (a -> a)
traceWhenEnabled place logger =
    case place of
        D_Generic _ debugResult -> logger debugResult
        _ -> case Map.lookup place enabledPlaces of
            Nothing -> id
            Just debugResult -> logger debugResult

{-|Wraps an 'ExceptT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceExceptT
    :: (Monad m, Show a, Show b)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> ExceptT a m b
    -- ^ Action to wrap
    -> ExceptT a m b
traceExceptT name startValues =
    traceWhenEnabled name (traceExceptTS (show name) startValues)

traceExceptTS
    :: (Monad m, Show a, Show b)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> ExceptT a m b
    -- ^ Action to wrap
    -> ExceptT a m b
traceExceptTS name startValues debugResult action = ExceptT $ do
    result <-
        startThing name startValues
        $ runExceptT action
    case result of
        Left err ->
            endThing name ("error: " ++ show err) debugResult
            $ return (Left err)
        Right r ->
            endThing name ("result: " ++ show r) debugResult
            $ return (Right r)

{-|Wraps a 'MaybeT' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceMaybeT
    :: (Monad m, Show a)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> MaybeT m a
    -- ^ Action to wrap
    -> MaybeT m a
traceMaybeT name startValues =
    traceWhenEnabled
        name
        (traceMaybeTS (show name) startValues)

traceMaybeTS
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> MaybeT m a
    -- ^ Action to wrap
    -> MaybeT m a
traceMaybeTS name startValues debugResult action = MaybeT $ do
    result <- startThing name startValues $ runMaybeT action
    case result of
        Nothing ->
            endThing name "nothing" debugResult
            $ return Nothing
        Just r ->
            endThing name ("result: " ++ show r) debugResult
            $ return (Just r)

{-|Wraps an 'Either' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceEither
    :: (Show a, Show b)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> Either a b
    -- ^ Action to wrap
    -> Either a b
traceEither name startValues =
    traceWhenEnabled
        name
        (traceEitherS (show name) startValues)

traceEitherS
    :: (Show a, Show b)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> Either a b
    -- ^ Action to wrap
    -> Either a b
traceEitherS name startValues debugResult action =
    startThing name startValues
    $ case action of
        Left err ->
            endThing name ("error: " ++ show err) debugResult
            $ Left err
        Right r ->
            endThing name ("result: " ++ show r) debugResult
            $ Right r

{-|Wraps a 'Maybe' action for printing debug messages, similar to 'trace'.

It prints the name and the start values before the action, and the action
result after.
-}
traceMaybe
    :: Show a
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> Maybe a
    -- ^ Action to wrap
    -> Maybe a
traceMaybe name startValues =
    traceWhenEnabled
        name
        (traceMaybeS (show name) startValues)

traceMaybeS
    :: Show a
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> Maybe a
    -- ^ Action to wrap
    -> Maybe a
traceMaybeS name startValues debugResult action =
    startThing name startValues
    $ case action of
        Nothing ->
            endThing name "Nothing" debugResult Nothing
        Just r ->
            endThing name ("result: " ++ show r) debugResult
            $ Just r

{-|Wraps a generic monad action for printing debug messages, similar to 'trace'.

The monad must not have an error case because this function will
not print an "ending ..." line for errors, making the output confusing
and ruining the indentation produced by debugFilter.py.

It prints the name and the start values before the action, and the action
result after.
-}
traceNonErrorMonad
    :: (Monad m, Show a)
    => DebugPlace
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> m a
    -- ^ Action to wrap
    -> m a
traceNonErrorMonad name startValues =
    traceWhenEnabled
        name
        (traceNonErrorMonadS (show name) startValues)

traceNonErrorMonadS
    :: (Monad m, Show a)
    => String
    -- ^ Action name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> m a
    -- ^ Action to wrap
    -> m a
traceNonErrorMonadS name startValues debugResult action =
    startThing name startValues
    $ do
        result <- action
        endThing name ("result: " ++ show result) debugResult
            $ return result

{-|Wraps a function for printing debug messages, similar to 'Debug.trace'.

It prints the name and the start values before evaluating the function,
and the function result after.
-}
traceFunction
    :: (Show a)
    => DebugPlace
    -- ^ function name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> a
    -- function result
    -> a
traceFunction name startValues =
    traceWhenEnabled
        name
        (traceFunctionS (show name) startValues)

traceFunctionS
    :: (Show a)
    => String
    -- ^ function name
    -> [DebugArg]
    -- ^ Extra debugging info (usually the inputs)
    -> DebugResult
    -> a
    -- function result
    -> a
traceFunctionS name startValues debugResult result =
    startThing name startValues
    $ endThing name ("result: " ++ show result) debugResult result

startThing :: String -> [DebugArg] -> a -> a
startThing name startValues =
    trace ("starting " ++ name ++ " with (" ++ formatted ++ ")")
  where
    formatted = intercalate "," (map show startValues)

endThing :: String -> String -> DebugResult -> a -> a
endThing name result debugResult =
    trace ("ending " ++ name ++ resultMesasge)
  where
    resultMesasge = case debugResult of
        DebugResult -> " with " ++ result
        DebugNoResult -> ""


{- | Insert a separator between the items and enclose them with the delimiters.

When the document is grouped with 'Pretty.group' and fits on one line, the
delimiters are set off by one space,

@
[ A, B, C ]
@

Otherwise, the delimiters and separators are placed at the beginning of each
line,

@
[ A
, B
, C
]
@

 -}
encloseSep
    :: Doc ann   -- ^ Left delimiter
    -> Doc ann   -- ^ Right delimiter
    -> Doc ann   -- ^ Separator
    -> [Doc ann] -- ^ Items
    -> Doc ann
encloseSep ldelim rdelim sep =
    \case
        [] -> ldelim <> rdelim
        (doc : docs) ->
            mconcat $ concat
                [ [ldelim <+> doc]
                , map ((Pretty.line' <> sep) <+>) docs
                , [Pretty.line, rdelim]
                ]

-- | Surround the second argument with parentheses if needed.
parens
    :: Bool  -- ^ Needs parentheses
    -> Doc ann
    -> Doc ann
parens needsParens
  | needsParens  = Pretty.parens
  | otherwise    = id

{- | 'Debug' prints data for debugging.

'debug' should produce correct Haskell source syntax so that debugged values can
be easily loaded into GHCi, i.e. @debug@ should obey

@
  read . show . debug === id
@

 -}
class Debug a where
    debug :: a -> Doc ann
    debug = \a -> debugPrec a 0

    debugPrec :: a -> Int -> Doc ann
    default debugPrec
        :: (Generic a, HasDatatypeInfo a, All2 Debug (Code a))
        => a
        -> Int  -- ^ surrounding precedence
        -> Doc ann
    debugPrec = debugPrecGeneric

debugPrecGeneric
    :: forall a ann
    .  (Generic a, HasDatatypeInfo a, All2 Debug (Code a))
    => a
    -> Int  -- ^ Surrounding precedence
    -> Doc ann
debugPrecGeneric a =
    debugPrecAux (SOP.datatypeInfo $ Proxy @a) (debugSOP (SOP.from a))

debugPrecAux
    :: forall xss ann
    .  (All SOP.Top xss)
    => DatatypeInfo xss
    -> SOP (K (Int -> Doc ann)) xss
    -> Int  -- ^ Surrounding precedence
    -> Doc ann
debugPrecAux datatypeInfo (SOP sop) =
    SOP.hcollapse $ SOP.hzipWith debugConstr constrs sop
  where
    constrs :: NP ConstructorInfo xss
    constrs =
        case datatypeInfo of
            SOP.ADT     _ _ cs -> cs
            SOP.Newtype _ _ c  -> c :* Nil

precConstr, precRecord :: Int
precConstr = 10  -- precedence of function application
precRecord = 11  -- precedence of record syntax

debugConstr
    :: ConstructorInfo xs  -- ^ Constructor
    -> NP (K (Int -> Doc ann)) xs             -- ^ Arguments
    -> K (Int -> Doc ann) xs

debugConstr (SOP.Constructor name) args =
    K $ \precOut ->
        parens (precOut >= precConstr && (not . null) args')
        . Pretty.nest 4
        $ Pretty.sep (name' : args')
  where
    name' = parens needsParens (Pretty.pretty name)
      where
        initial = head name
        needsParens = (not . Char.isLetter) initial && initial /= '('
    args' = map ($ precConstr) (SOP.hcollapse args)

debugConstr (SOP.Infix name _ precInfix) (K x :* K y :* Nil) =
    K $ \precOut ->
        parens (precOut >= precInfix)
        . Pretty.nest 4
        $ Pretty.sep [x precInfix, Pretty.pretty name, y precInfix]

debugConstr (SOP.Record name fields) args =
    K $ \precOut ->
        parens (precOut >= precRecord)
        . Pretty.align . Pretty.nest 4 . Pretty.group
        $ mconcat
            [ Pretty.pretty name
            , Pretty.line
            , encloseSep Pretty.lbrace Pretty.rbrace Pretty.comma args'
            ]
  where
    args' = SOP.hcollapse $ SOP.hzipWith debugField fields args

    debugField :: FieldInfo x -> K (Int -> Doc ann) x -> K (Doc ann) x
    debugField (FieldInfo fieldName) (K arg) =
        K $ Pretty.nest 4 $ Pretty.sep
            [ Pretty.pretty fieldName Pretty.<+> "="
            , arg 0
            ]

debugSOP
    :: forall xss ann
    .  All2 Debug xss
    => SOP I xss
    -> SOP (K (Int -> Doc ann)) xss
debugSOP (SOP sop) =
    SOP $ SOP.hcmap pAllDebug (SOP.hcmap pDebug (SOP.mapIK debugPrec)) sop
  where
    pDebug = Proxy :: Proxy Debug
    pAllDebug = Proxy :: Proxy (All Debug)

instance Debug a => Debug [a] where
    debugPrec as _ =
        Pretty.group
        . encloseSep Pretty.lbracket Pretty.rbracket Pretty.comma
        $ map debug as

instance {-# OVERLAPS #-} Debug String where
    debugPrec a = \p -> Pretty.pretty (showsPrec p a "")

instance Debug Text where
    debugPrec a = \p -> Pretty.pretty (showsPrec p a "")

instance Debug Void

instance Debug ()

instance (Debug a, Debug b) => Debug (a, b)

instance Debug Natural where
    debugPrec x = \_ -> Pretty.pretty x

instance Debug Integer where
    debugPrec x = \_ -> parens (x < 0) (Pretty.pretty x)

instance Debug Int where
    debugPrec x = \_ -> parens (x < 0) (Pretty.pretty x)

instance Debug Char where
    debugPrec x = \_ -> Pretty.squotes (Pretty.pretty x)

instance Debug a => Debug (Maybe a)

instance Debug a => Debug (Sup a)

instance Debug a => Debug (Identity a)

instance (Debug a, Debug (f b)) => Debug (CofreeF f a b) where
    debugPrec (a :< fb) =
        -- Cannot have orphan instances of Generic and HasDatatypeInfo.
        -- Use a fake instance instead.
        debugPrecAux datatypeInfo (debugSOP sop)
      where
        datatypeInfo =
            SOP.ADT
                "Control.Comonad.Trans.Cofree"
                "CofreeF"
                (constrInfo :* Nil)
        constrInfo = SOP.Infix ":<" SOP.RightAssociative 5
        sop = SOP (Z (I a :* I fb :* Nil))

instance
    (Debug a, Debug (w (CofreeF f a (CofreeT f w a)))) =>
    Debug (CofreeT f w a)
  where
    debugPrec (CofreeT x) =
        -- Cannot have orphan instances of Generic and HasDatatypeInfo.
        -- Use a fake instance instead.
        debugPrecAux datatypeInfo (debugSOP sop)
      where
        datatypeInfo =
            SOP.Newtype
                "Control.Comonad.Trans.Cofree"
                "CofreeT"
                constrInfo
        constrInfo = SOP.Record "CofreeT" (FieldInfo "runCofreeT" :* Nil)
        sop = SOP (Z (I x :* Nil))

instance (Debug k, Debug a) => Debug (Map.Map k a) where
    debugPrec as precOut =
        parens (precOut >= 10) ("Data.Map.fromList" <+> debug (Map.toList as))

instance Debug a => Debug (Set a) where
    debugPrec as precOut =
        parens (precOut >= 10) ("Data.Set.fromList" <+> debug (Set.toList as))

instance Debug a => Debug (Seq a) where
    debugPrec as precOut =
        parens (precOut >= 10)
        $ "Data.Sequence.fromList" <+> debug (Foldable.toList as)

instance Debug a => Debug (Const a b)

instance Debug Bool

instance Debug SExpr

instance Debug GHC.CallStack

instance Debug GHC.SrcLoc

{- | 'Diff' displays the difference between values for debugging.

@diff@ and @diffPrec@ should generally display the /minimal/ difference between
two values, as far as it is practical to do so. Like 'debug', @diff@ and
@diffPrec@ should produce valid Haskell source syntax to facilitate
debugging. To elide the identical parts of two values, use holes (@_@).

A default implementation is provided for @diffPrec@ by @diffPrecGeneric@, which
only requires some instances to be derived:

> data DataType = ...
>     deriving (GHC.Generics.Generic)
>
> instance Generics.SOP.Generic DataType
>
> instance Generics.SOP.HasDatatypeInfo DataType
>
> instance Debug DataType
>
> instance Diff DataType

 -}
class Debug a => Diff a where
    diff :: a -> a -> Maybe (Doc ann)
    diff a b = ($ 0) <$> diffPrec a b

    {- | Display the difference of two values.

    If the values are different, the difference is displayed given the
    surrounding precedence.

     -}
    diffPrec :: a -> a -> Maybe (Int -> Doc ann)
    default diffPrec
        :: (Generic a, HasDatatypeInfo a, All2 Diff (Code a))
        => a
        -> a
        -> Maybe (Int -> Doc ann)
    diffPrec = diffPrecGeneric

{- | Default implementation of 'diffPrec' for instances of 'Eq'.

For any type which is 'Eq' and 'Debug', @diffPrecEq@ provides a default
implementation of 'diffPrec'. If the values differ, the entirety of both values
is displayed using 'Debug'; this is most suitable for atomic types, like
'Integer', or short strings.

 -}
diffPrecEq
    :: (Debug a, Eq a)
    => a -> a -> Maybe (Int -> Doc ann)
diffPrecEq a b
  | a == b    = Nothing
  | otherwise =
    Just $ \p ->
        Pretty.sep
            [ "{- was:"
            , debugPrec a p
            , "-}"
            , debugPrec b p
            ]

{- | Default implementation of 'diffPrec' for instances of 'Generic'.

@diffPrecGeneric@ uses the 'DatatypeInfo' of a 'Generic' type to print the
difference between two values. The arguments must also be instances of 'Debug',
which is used to print the values when they have different constructors. If they
have the same constructor, 'Generic' is used to examine its fields and minimize
the difference.

 -}
diffPrecGeneric
    :: forall a ann
    .  (Debug a, Generic a, HasDatatypeInfo a, All2 Diff (Code a))
    => a
    -> a
    -> Maybe (Int -> Doc ann)
diffPrecGeneric a b =
    diffNS constrs aNS bNS
  where
    constrs :: NP ConstructorInfo (Code a)
    constrs =
        case SOP.datatypeInfo (Proxy @a) of
            SOP.ADT     _ _ cs -> cs
            SOP.Newtype _ _ c  -> c :* Nil

    SOP aNS = SOP.from a
    SOP bNS = SOP.from b

    diffNS
        :: forall xss
        .  All2 Diff xss
        => NP ConstructorInfo xss
        -> NS (NP I) xss
        -> NS (NP I) xss
        -> Maybe (Int -> Doc ann)
    diffNS (c :* _) (Z aNP) (Z bNP) = diffNP c aNP bNP
    diffNS (_ :* cs) (S aNS') (S bNS') = diffNS cs aNS' bNS'
    diffNS _ _ _ =
        Just $ \precOut ->
            Pretty.sep
                [ "{- was:"
                , debugPrec a precOut
                , "-}"
                , debugPrec b precOut
                ]

    diffNP
        :: forall xs
        .  All Diff xs
        => ConstructorInfo xs
        -> NP I xs
        -> NP I xs
        -> Maybe (Int -> Doc ann)
    diffNP c aNP bNP
      | anyNP (isJust . SOP.unK) cNP =
        Just $ SOP.unK $ debugConstr c (SOP.hmap (SOP.mapKK maybeHole) cNP)
      | otherwise =
        Nothing
      where
        cNP = diffNP' aNP bNP
        maybeHole = fromMaybe (const "_")

    anyNP :: forall f xs. (forall x. f x -> Bool) -> NP f xs -> Bool
    anyNP query (fx :* fxs) = query fx || anyNP query fxs
    anyNP _ Nil = False

    diffNP'
        :: forall xs
        .  All Diff xs
        => NP I xs
        -> NP I xs
        -> NP (K (Maybe (Int -> Doc ann))) xs
    diffNP' = SOP.hczipWith (Proxy @Diff) (SOP.mapIIK diffPrec)

instance Diff Bool where
    diffPrec = diffPrecEq

instance Diff a => Diff [a]

instance {-# OVERLAPS #-} Diff String where
    diffPrec = diffPrecEq

instance Diff Text where
    diffPrec = diffPrecEq

instance Diff Void where
    diffPrec = diffPrecEq

instance Diff () where
    diffPrec = diffPrecEq

instance Diff Natural where
    diffPrec = diffPrecEq

instance Diff Integer where
    diffPrec = diffPrecEq

instance Diff Int where
    diffPrec = diffPrecEq

instance Diff Char where
    diffPrec = diffPrecEq

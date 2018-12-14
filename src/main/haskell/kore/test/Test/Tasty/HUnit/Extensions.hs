module Test.Tasty.HUnit.Extensions where

import Test.Tasty.HUnit
       ( assertBool, assertFailure )

import Control.Exception
       ( SomeException, catch, evaluate )
import Control.Monad
import Data.CallStack
import Data.Functor.Foldable
import Data.List
       ( intercalate, isInfixOf )

import           Kore.Reflect
                 ( Reflectable (reflect) )
import qualified Kore.Reflect as Reflect
import           Kore.Reflect.Transform
                 ( Transformation (Transformation), transform )
import           Kore.Reflect.Transformations
                 ( removeIdLocation )

assertEqualWithPrinter
    :: (Eq a, HasCallStack)
    => (a -> String)
    -> String -- ^ The message prefix
    -> a      -- ^ The expected value
    -> a      -- ^ The actual value
    -> IO ()
assertEqualWithPrinter printer preface expected actual =
    unless (actual == expected) (assertFailure msg)
  where
    msg =
        (if null preface then "" else preface ++ "\n")
        ++ "expected: " ++ printer expected ++ "\n but got: " ++ printer actual

assertInListP
    :: (Eq a, HasCallStack)
    => (a -> String)
    -> String -- ^ The message prefix
    -> [a]    -- ^ The expected value list
    -> a      -- ^ The actual value
    -> IO ()
assertInListP printer message expectedList actual =
    foldr
        (\ expected -> unless (expected == actual))
        (assertFailure ("No match for: " ++ printer actual ++ "\n" ++ message))
        expectedList

assertInList
    :: (Eq a, Show a, HasCallStack)
    => String -- ^ The message prefix
    -> [a]    -- ^ The expected value list
    -> a      -- ^ The actual value
    -> IO ()
assertInList = assertInListP show

assertError :: HasCallStack => (String -> IO()) -> a -> IO()
assertError errorTest action = do
    maybeErr <-
        catch
            (do
                _ <- evaluate action
                return Nothing
            )
            (\err -> return (Just (show (err :: SomeException))))
    case maybeErr of
        Nothing  -> assertFailure "No error during action."
        Just err -> errorTest err

assertSubstring :: HasCallStack => String -> String -> String -> IO()
assertSubstring message first second =
    assertBool
        (  message
        ++ ": '"
        ++ first
        ++ "' is not a substring of '"
        ++ second
        ++ "'"
        )
        (first `isInfixOf` second)

{-| 'EqualWithExplanation' is a class for objects that can be compared for
equality, and for which an explanation of an equality failure is desired.

This can be used with, e.g., assertEqualWithExplanation.
-}
class EqualWithExplanation a where
    {-| 'compareWithExplanation' compares two values, returning Nothing
    if they are equal or (Just explanation) if they are different.

    This explanation is assumed to be a human readable representation of the
    two input values that highlights why they are not equal. As an example,
    whn comparing (a, b) with (a, c), this function may return
    (..., b <vs> c).
    -}
    compareWithExplanation :: a -> a -> Maybe String
    {-| 'printWithExplanation' should display the data passed to it.
    TODO: Consider removing it and using 'show'.
    -}
    printWithExplanation :: a -> String

assertEqualWithExplanation
    :: (EqualWithExplanation a, HasCallStack)
    => String -- ^ The message prefix
    -> a      -- ^ The expected value
    -> a      -- ^ The actual value
    -> IO ()
assertEqualWithExplanation prefix expected actual =
    case compareWithExplanation expected actual of
        Just explanation ->
            assertFailure
                ((if null prefix then "" else prefix ++ "\n") ++ explanation)
        Nothing -> pure ()

data EqWrap = forall a . EqualWithExplanation a => EqWrap String a a

formatDiffForExplanation :: String -> String -> String
formatDiffForExplanation expected actual =
    "\n    " ++ expected ++"\n***vs***\n    " ++ actual ++ "\n"

instance Reflectable a => EqualWithExplanation a where
    compareWithExplanation thing1 thing2 =
        compareReflectable
            (normalize (reflect thing1)) (normalize (reflect thing2))
      where
        normalize = transform (Transformation [removeIdLocation])
    printWithExplanation = Reflect.printData . reflect

compareReflectable
    :: Reflect.RecursiveData -> Reflect.RecursiveData -> Maybe String
compareReflectable
    (Fix (Reflect.Sum Reflect.ProductElement {name = name1, values = values1}))
    (Fix (Reflect.Sum Reflect.ProductElement {name = name2, values = values2}))
  | name1 == name2 = do -- Maybe monad
    err <- compareList "" "" values1 values2
    return ("(" ++ name1 ++ " " ++ err ++ ")")
  | otherwise =
    Just (formatDiffForExplanation name1 name2)
compareReflectable
    (Fix (Reflect.Struct
        Reflect.ProductElement {name = name1, values = values1}
    ))
    (Fix (Reflect.Struct
        Reflect.ProductElement {name = name2, values = values2}
    ))
  | name1 == name2 = do -- Maybe monad
    err <- compareStructList values1 values2
    return (name1 ++ " {" ++ err ++ "}")
  | otherwise =
    error ("Expected the same name, got " ++ show [name1, name2])
compareReflectable
    (Fix (Reflect.StructField name1 value1))
    (Fix (Reflect.StructField name2 value2))
  | name1 == name2 = do -- Maybe monad
    err <- compareReflectable value1 value2
    return (name1 ++ "=" ++ err)
  | otherwise =
    Just (formatDiffForExplanation name1 name2)
compareReflectable
    (Fix (Reflect.Value value1))
    (Fix (Reflect.Value value2))
  | value1 == value2 = Nothing
  | otherwise = Just (formatDiffForExplanation value1 value2)
compareReflectable
    (Fix (Reflect.List values1))
    (Fix (Reflect.List values2))
  = compareList "[" "]" values1 values2
compareReflectable
    (Fix (Reflect.Tuple values1))
    (Fix (Reflect.Tuple values2))
  = compareList "(" ")" values1 values2
compareReflectable
    (Fix Reflect.Deleted)
    (Fix Reflect.Deleted)
  = Nothing

compareReflectable expected actual
  | expected == actual =
    error
        (  "We should not reach this line with equal data: "
        ++ show expected
        )
  | otherwise =
    Just
        (formatDiffForExplanation
            (Reflect.printData expected) (Reflect.printData actual)
        )

compareStructList
    :: [Reflect.RecursiveData]
    -> [Reflect.RecursiveData]
    -> Maybe String
compareStructList l1 l2
  | length l1 == length l2 =
    case foldl compareStructListElement (Right []) (zip l1 l2) of
        Right _   -> Nothing
        Left diff -> Just (intercalate ", " (reverse diff))
  | otherwise =
    error
        (  "expected same length lists, but got "
        ++ show [length l1, length l2]
        )

compareStructListElement
    :: Either [String] [String]
    ->  ( Reflect.RecursiveData, Reflect.RecursiveData )
    -> Either [String] [String]
compareStructListElement (Left diff) _ =
    Left ("..." : diff)
compareStructListElement
    (Right same)
    (data1, data2)
  = case compareReflectable data1 data2 of
        Just diff -> Left (diff : same)
        Nothing   -> Right ("..." : same)

compareList
    :: String -> String
    -> [Reflect.RecursiveData]
    -> [Reflect.RecursiveData]
    -> Maybe String
compareList start end expected actual =
    case compareUnequalList expected actual of
        Left _     -> Nothing
        Right errs -> Just (start ++ intercalate ", " errs ++ end)

compareUnequalList
    :: [Reflect.RecursiveData]
    -> [Reflect.RecursiveData]
    -> Either () [String]
compareUnequalList [] [] = Left ()
compareUnequalList (expect : es) [] =
    Right
        [ formatDiffForExplanation
            (  Reflect.printData expect
            ++ intercalate ", " (map (const "...") es)
            )
            "<nothing>"
        ]
compareUnequalList [] (act : as) =
    Right
        [ formatDiffForExplanation
            "<nothing>"
            (  Reflect.printData act
            ++ intercalate ", " (map (const "...") as)
            )
        ]
compareUnequalList (expect : es) (act : as) =
    case compareReflectable expect act of
        Just diff ->
            Right [diff, "..."]
        Nothing -> do
            diff <- compareUnequalList es as
            return ("..." : diff)

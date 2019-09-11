module Test.Kore.Internal.Symbol
    ( symbolGen
    ) where

import qualified Hedgehog.Gen as Gen

import qualified Data.Default as Default

import qualified Kore.Attribute.Symbol as Attribute
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
import Kore.Sort

import Test.Kore
    ( Gen
    , couple
    , idGen
    , sortGen
    )

symbolGen :: Sort -> Gen Symbol
symbolGen resultSort =
    Symbol
        <$> Gen.small idGen
        <*> couple (Gen.small sortGen)
        <*> applicationSortsGen resultSort
        <*> symbolAttributeGen

applicationSortsGen :: Sort -> Gen ApplicationSorts
applicationSortsGen resultSort =
    ApplicationSorts
        <$> couple (Gen.small sortGen)
        <*> pure resultSort

symbolAttributeGen :: Gen Attribute.Symbol
symbolAttributeGen =
    Attribute.Symbol
        <$> functionAttributeGen
        <*> functionalAttributeGen
        <*> constructorAttributeGen
        <*> injectiveAttributeGen
        <*> sortInjectionAttributeGen
        <*> anywhereAttributeGen
        <*> hookAttributeGen
        <*> smtlibAttributeGen
        <*> smthookAttributeGen
        <*> memoAttributeGen

functionAttributeGen :: Gen Attribute.Function
functionAttributeGen = Attribute.Function <$> Gen.bool

functionalAttributeGen :: Gen Attribute.Functional
functionalAttributeGen = Attribute.Functional <$> Gen.bool

constructorAttributeGen :: Gen Attribute.Constructor
constructorAttributeGen = Attribute.Constructor <$> Gen.bool

injectiveAttributeGen :: Gen Attribute.Injective
injectiveAttributeGen = Attribute.Injective <$> Gen.bool

sortInjectionAttributeGen :: Gen Attribute.SortInjection
sortInjectionAttributeGen = Attribute.SortInjection <$> Gen.bool

anywhereAttributeGen :: Gen Attribute.Anywhere
anywhereAttributeGen = Attribute.Anywhere <$> Gen.bool

hookAttributeGen :: Gen Attribute.Hook
hookAttributeGen = pure Default.def

smtlibAttributeGen :: Gen Attribute.Smtlib
smtlibAttributeGen = pure Default.def

smthookAttributeGen :: Gen Attribute.Smthook
smthookAttributeGen = pure Default.def

memoAttributeGen :: Gen Attribute.Memo
memoAttributeGen = Attribute.Memo <$> Gen.bool

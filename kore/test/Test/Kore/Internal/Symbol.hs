module Test.Kore.Internal.Symbol (
    symbolGen,
) where

import Data.Default qualified as Default
import Hedgehog.Gen qualified as Gen
import Kore.Attribute.SourceLocation
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
import Kore.Sort
import Prelude.Kore
import Test.Kore (
    Gen,
    couple,
    idGen,
    sortGen,
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
        <*> totalAttributeGen
        <*> constructorAttributeGen
        <*> injectiveAttributeGen
        <*> sortInjectionAttributeGen
        <*> anywhereAttributeGen
        <*> hookAttributeGen
        <*> smtlibAttributeGen
        <*> smthookAttributeGen
        <*> memoAttributeGen
        <*> klabelAttributeGen
        <*> symbolKywdAttributeGen
        <*> noEvaluatorsAttributeGen
        <*> sourceLocationAttributeGen
        <*> macroAttributeGen
        <*> aliasKywdAttributeGen

functionAttributeGen :: Gen Attribute.Function
functionAttributeGen = Attribute.Function <$> Gen.bool

totalAttributeGen :: Gen Attribute.Total
totalAttributeGen = Attribute.Total <$> Gen.bool

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

klabelAttributeGen :: Gen Attribute.Klabel
klabelAttributeGen = pure Default.def

symbolKywdAttributeGen :: Gen Attribute.SymbolKywd
symbolKywdAttributeGen = Attribute.SymbolKywd <$> Gen.choice [pure Nothing, pure $ Just "", pure $ Just "aSymbol"]

noEvaluatorsAttributeGen :: Gen Attribute.NoEvaluators
noEvaluatorsAttributeGen = Attribute.NoEvaluators <$> Gen.bool

sourceLocationAttributeGen :: Gen Kore.Attribute.SourceLocation.SourceLocation
sourceLocationAttributeGen = pure Default.def

macroAttributeGen :: Gen Attribute.Macro
macroAttributeGen = Attribute.Macro <$> Gen.bool

aliasKywdAttributeGen :: Gen Attribute.AliasKywd
aliasKywdAttributeGen = Attribute.AliasKywd <$> Gen.bool

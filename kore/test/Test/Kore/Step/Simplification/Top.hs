module Test.Kore.Step.Simplification.Top
    ( --t-est_topSimplification
    ) where
{-
import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Step.Simplification.Top
    ( simplify
    )
import Kore.Syntax
    ( Sort
    , Top (Top)
    , Variable
    )
import qualified Kore.Syntax as Syntax.DoNotUse


import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

t-est_topSimplification :: [TestTree]
t-est_topSimplification =
    [ testCase "Top evaluates to top"
        (assertEqual ""
            Pattern.top
            (evaluate Top { topSort = testSort })
        )
    ]

evaluate :: Top Sort (OrPattern Variable) -> Pattern Variable
evaluate = simplify
-}

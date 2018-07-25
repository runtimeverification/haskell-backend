{-# OPTIONS_GHC
    -F -pgmF tasty-discover
    -optF --tree-display
    -optF --ingredient=Test.Tasty.Runners.consoleTestReporter
    -optF --ingredient=Test.Tasty.Runners.listingTests
    -optF --ingredient=Test.Tasty.Runners.AntXML.antXMLRunner
#-}

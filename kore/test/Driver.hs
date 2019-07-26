{-# OPTIONS_GHC -F -pgmF tasty-discover -optF --tree-display -optF --hide-successes -optF --ingredient=Test.Tasty.Runners.consoleTestReporter -optF --ingredient=Test.Tasty.Runners.listingTests -optF --ingredient=Test.Tasty.Runners.AntXML.antXMLRunner -optF --generated-module=Driver #-}

{- |

* Debugging

If building the test suite fails with some undecipherable error, add

> -optF --debug

to the `OPTION_GHC` pragma above. The option will cause `tasty-debug` to print
the generated source code to the terminal; hopefully, this reveals the error.

-}

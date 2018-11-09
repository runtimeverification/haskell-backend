module Kore.Builtin.Error
    ( verifierBug
    , wrongArity
    ) where

import GHC.Stack
       ( HasCallStack )

{- | Abort due to an internal error that should be prevented by the verifier.

    Such an error is a bug in Kore that we would like the user to report.

 -}
verifierBug :: HasCallStack => String -> a
verifierBug msg =
    (error . unlines)
        [ "Internal error: " ++ msg
        , "This error should be prevented by the verifier."
        , "Please report this as a bug."
        ]

{- | Evaluation failure due to a builtin call with the wrong arity.

 -}
wrongArity :: HasCallStack => String -> a
wrongArity ctx = verifierBug (ctx ++ ": Wrong number of arguments")

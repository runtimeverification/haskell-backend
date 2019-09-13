{- |
Module      : Kore.Builtin.Error
Description : Errors related to builtin domain verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

This module defines reusable error conditions to be triggered when a bug in the
pattern verifier has admitted an invalid builtin domain expression.

 -}
module Kore.Builtin.Error
    ( verifierBug
    , wrongArity
    , notImplementedInternal
    ) where

import GHC.Stack
    ( HasCallStack
    )

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

{- | Throw an error for operations not implemented for internal domain values.
 -}
notImplementedInternal :: HasCallStack => a
notImplementedInternal = error "Not implemented for internal domain values"

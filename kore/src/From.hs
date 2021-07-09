{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module From (
    From (..),
    into,
) where

import Data.Sequence (
    Seq,
 )
import qualified Data.Sequence as Seq
import Data.Void

{- | Convert type @from@ into @to@.

Valid instances are /total/. @from@ should be a homomorphism
(structure-preserving map); what structure is preserved shall be determined by
the implementer.

Usage with @TypeApplications@:

@
let b = let a = _ in from @A @B a
@

Usage with both types inferred:

@
let b :: B = let a :: A = _ in from a
@

Usage with only @to@ inferred:

@
let b :: B = let a = _ in from @A a
@

Usage with only @from@ inferred:

@
let b = let a :: A = _ in from @_ @B a
@
-}
class From from to where
    from :: from -> to

-- | @into@ is 'from' with the type parameters in reverse order.
into :: forall to from. From from to => from -> to
into = from @from @to

-- | This instance implements the principle /ex falso quodlibet/.
instance From Void any where
    from = absurd
    {-# INLINE from #-}

instance From [a] (Seq a) where
    from = Seq.fromList
    {-# INLINE from #-}

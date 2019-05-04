module Test.Kore.Debug where

import Test.Tasty

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.String as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

import qualified Test.Terse as Terse

-- A simple type with one constructor
data A = A deriving GHC.Generic

instance SOP.Generic A

instance SOP.HasDatatypeInfo A

instance Debug A

-- A simple type with one constructor
data B = B deriving GHC.Generic

instance SOP.Generic B

instance SOP.HasDatatypeInfo B

instance Debug B

-- A record type
data R = R { rA :: A, rB :: B }
    deriving GHC.Generic

instance SOP.Generic R

instance SOP.HasDatatypeInfo R

instance Debug R

-- A sum type with unary constructors
data S = SA A | SB B deriving GHC.Generic

instance SOP.Generic S

instance SOP.HasDatatypeInfo S

instance Debug S

-- A product type with one constructor
data P = P A B deriving GHC.Generic

instance SOP.Generic P

instance SOP.HasDatatypeInfo P

instance Debug P

-- A complex algebraic data type
data D = D S P deriving GHC.Generic

instance SOP.Generic D

instance SOP.HasDatatypeInfo D

instance Debug D

-- A product type with an infix constructor
data I = S ::: S deriving GHC.Generic

infixl 7 :::

instance SOP.Generic I

instance SOP.HasDatatypeInfo I

instance Debug I

-- A product type with a prefix constructor and an auxiliary fixity declaration
data I' = (::::) S S deriving GHC.Generic

infixl 7 ::::

instance SOP.Generic I'

instance SOP.HasDatatypeInfo I'

instance Debug I'

-- A newtype
newtype N = N B deriving GHC.Generic

instance SOP.Generic N

instance SOP.HasDatatypeInfo N

instance Debug N

-- A record newtype
newtype Rn = Rn { unRn :: A } deriving GHC.Generic

instance SOP.Generic Rn

instance SOP.HasDatatypeInfo Rn

instance Debug Rn

test_debug :: [TestTree]
test_debug =
    [ A                          `yields` "A"
    , B                          `yields` "B"
    , ()                         `yields` "()"
    , ("Hello world!" :: String) `yields` "\"Hello world!\""
    , [A, A, A]                  `yields` "[A, A, A]"
    , (A, B)                     `yields` "(,) A B"
    , R { rA = A, rB = B }       `yields` "R { rA = A, rB = B }"
    , SA A                       `yields` "SA A"
    , SB B                       `yields` "SB B"
    , P A B                      `yields` "P A B"
    , D (SA A) (P A B)           `yields` "D (SA A) (P A B)"
    , D (SB B) (P A B)           `yields` "D (SB B) (P A B)"
    , (SA A ::: SB B)            `yields` "SA A ::: SB B"
    , (SA A :::: SB B)           `yields` "(::::) (SA A) (SB B)"
    , N B                        `yields` "N B"
    , Rn { unRn = A }            `yields` "Rn { unRn = A }"
    ]
  where
    yields input = Terse.equals_ (render $ debug input)
    render = Pretty.renderString . layout
    layout =
        Pretty.layoutSmart
            Pretty.LayoutOptions { layoutPageWidth = Pretty.Unbounded }

test_debugPrec :: [TestTree]
test_debugPrec =
    [ A                          `yields` "A"
    , B                          `yields` "B"
    , ()                         `yields` "()"
    , ("Hello world!" :: String) `yields` "\"Hello world!\""
    , [A, A, A]                  `yields` "[A, A, A]"
    , (A, B)                     `yields` "((,) A B)"
    , R { rA = A, rB = B }       `yields` "R { rA = A, rB = B }"
    , SA A                       `yields` "(SA A)"
    , SB B                       `yields` "(SB B)"
    , P A B                      `yields` "(P A B)"
    , D (SA A) (P A B)           `yields` "(D (SA A) (P A B))"
    , D (SB B) (P A B)           `yields` "(D (SB B) (P A B))"
    , (SA A ::: SB B)            `yields` "(SA A ::: SB B)"
    , (SA A :::: SB B)           `yields` "((::::) (SA A) (SB B))"
    , N B                        `yields` "(N B)"
    , Rn { unRn = A }            `yields` "Rn { unRn = A }"
    ]
  where
    yields input = Terse.equals_ (render $ debugPrec 10 input)
    render = Pretty.renderString . layout
    layout =
        Pretty.layoutSmart
            Pretty.LayoutOptions { layoutPageWidth = Pretty.Unbounded }

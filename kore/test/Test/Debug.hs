module Test.Debug where

import Test.Tasty

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.String as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Sort
import Kore.Syntax.Variable

import Test.Kore
import qualified Test.Terse as Terse

-- A simple type with one constructor
data A = A deriving GHC.Generic

instance SOP.Generic A

instance SOP.HasDatatypeInfo A

instance Debug A

instance Diff A

-- A simple type with one constructor
data B = B deriving GHC.Generic

instance SOP.Generic B

instance SOP.HasDatatypeInfo B

instance Debug B

instance Diff B

-- A record type
data R = R { rA :: A, rB :: B }
    deriving GHC.Generic

instance SOP.Generic R

instance SOP.HasDatatypeInfo R

instance Debug R

instance Diff R

-- A sum type with unary constructors
data S = SA A | SB B deriving GHC.Generic

instance SOP.Generic S

instance SOP.HasDatatypeInfo S

instance Debug S

instance Diff S

-- A product type with one constructor
data P = P A B deriving GHC.Generic

instance SOP.Generic P

instance SOP.HasDatatypeInfo P

instance Debug P

instance Diff P

-- A complex algebraic data type
data D = D S P deriving GHC.Generic

instance SOP.Generic D

instance SOP.HasDatatypeInfo D

instance Debug D

instance Diff D

-- A product type with an infix constructor
data I a b = a ::: b deriving GHC.Generic

infixl 7 :::

instance SOP.Generic (I a b)

instance SOP.HasDatatypeInfo (I a b)

instance (Debug a, Debug b) => Debug (I a b)

instance (Debug a, Debug b, Diff a, Diff b) => Diff (I a b)

-- A product type with a prefix constructor and an auxiliary fixity declaration
data I' = (::::) S S deriving GHC.Generic

infixl 7 ::::

instance SOP.Generic I'

instance SOP.HasDatatypeInfo I'

instance Debug I'

instance Diff I'

-- A newtype
newtype N a = N a deriving GHC.Generic

instance SOP.Generic (N a)

instance SOP.HasDatatypeInfo (N a)

instance Debug a => Debug (N a)

instance (Debug a, Diff a) => Diff (N a)

-- A record newtype
newtype Rn a = Rn { unRn :: a } deriving GHC.Generic

instance SOP.Generic (Rn a)

instance SOP.HasDatatypeInfo (Rn a)

instance Debug a => Debug (Rn a)

instance (Debug a, Diff a) => Diff (Rn a)


-- A record
data R3 a b c = R3 { fieldA :: a, fieldB :: b, fieldC :: c }
    deriving GHC.Generic

instance SOP.Generic (R3 a b c)

instance SOP.HasDatatypeInfo (R3 a b c)

instance (Debug a, Debug b, Debug c) => Debug (R3 a b c)

instance
    ( Debug a, Debug b, Debug c, Diff a, Diff b, Diff c )
    => Diff (R3 a b c)

test_debug :: [TestTree]
test_debug =
    [ A                          `yields` "A"
    , B                          `yields` "B"
    , ()                         `yields` "()"
    , ("Hello world!" :: String) `yields` "\"Hello world!\""
    , (0 :: Integer)             `yields` "0"
    , (1 :: Integer)             `yields` "1"
    , ((-1) :: Integer)          `yields` "(-1)"
    , (0 :: Int)                 `yields` "0"
    , (1 :: Int)                 `yields` "1"
    , ((-1) :: Int)              `yields` "(-1)"
    , [A, A, A]                  `yields` "[ A, A, A ]"
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
    , (0 :: Integer)             `yields` "0"
    , (1 :: Integer)             `yields` "1"
    , ((-1) :: Integer)          `yields` "(-1)"
    , (0 :: Int)                 `yields` "0"
    , (1 :: Int)                 `yields` "1"
    , ((-1) :: Int)              `yields` "(-1)"
    , [A, A, A]                  `yields` "[ A, A, A ]"
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
    yields input = Terse.equals_ (render $ debugPrec input 10)
    render = Pretty.renderString . layout
    layout =
        Pretty.layoutSmart
            Pretty.LayoutOptions { layoutPageWidth = Pretty.Unbounded }

test_Debug :: [TestTree]
test_Debug =
    [ Variable
        { variableName = testId "v"
        , variableCounter = mempty
        , variableSort = SortVariableSort (SortVariable (testId "sv"))
        }
        `yields`
        "Variable\n\
        \{ variableName = Id { getId = \"v\", idLocation = AstLocationTest }\n\
        \, variableCounter = Nothing\n\
        \, variableSort =\n\
        \    SortVariableSort\n\
        \        SortVariable\n\
        \        { getSortVariable = Id { getId = \"sv\", idLocation = AstLocationTest }\n\
        \        }\n\
        \}"
        $  "Variable"
    , Just (testId "v")
        `yields`
        "Just Id { getId = \"v\", idLocation = AstLocationTest }"
        $ "Maybe - Just"
    , (Nothing :: Maybe Id)
        `yields`
        "Nothing"
        $ "Maybe - Nothing"
    ]
  where
    yields input = Terse.equals (show $ debug input)

test_diff :: [TestTree]
test_diff =
    [ test (SA A, SA A)            $ Nothing
    , test (SA A, SB B)            $ Just "{- was: SA A -} SB B"
    , test (N (SA A), N (SB B))    $ Just "N {- was: (SA A) -} (SB B)"
    , test (Rn { unRn = SA A }, Rn { unRn = SB B })
        $ Just "Rn { unRn = {- was: SA A -} SB B }"
    , test ("A" :: String, "B")    $ Just "{- was: \"A\" -} \"B\""
    , test ('A', 'B')              $ Just "{- was: 'A' -} 'B'"
    , test (0 :: Integer, 1)       $ Just "{- was: 0 -} 1"
    , test (True, False)           $ Just "{- was: True -} False"
    , test ([True], [])            $ Just "{- was: [ True ] -} []"
    , test ([], [True])            $ Just "{- was: [] -} [ True ]"
    , test ([True], [True, False]) $ Just "_ : {- was: [] -} [ False ]"
    , test ([True, True], [True, False, True])
        $ Just "_ : ({- was: True -} False : {- was: [] -} [ True ])"
    , test
        ( R3 { fieldA = True , fieldB = True , fieldC = True }
        , R3 { fieldA = False, fieldB = False, fieldC = True }
        )
        $ Just "R3 { fieldA = {- was: True -} False, fieldB = {- was: True -} False, fieldC = _ }"
    , test
        ( R3 { fieldA = True, fieldB = True , fieldC = True }
        , R3 { fieldA = True, fieldB = False, fieldC = False }
        )
        $ Just "R3 { fieldA = _, fieldB = {- was: True -} False, fieldC = {- was: True -} False }"
    , test (True ::: False, True ::: True) $ Just "_ ::: {- was: False -} True"
    ]
  where
    test (a, b) = Terse.equals_ (render <$> diff a b)
    render = Pretty.renderString . layout
    layout =
        Pretty.layoutSmart
            Pretty.LayoutOptions { layoutPageWidth = Pretty.Unbounded }

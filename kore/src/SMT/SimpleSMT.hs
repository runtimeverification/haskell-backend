{-|
Module      : SimpleSMT
Description : Simple SMT-LIB 2 interface
Copyright   : (c) Iavor S. Diatchki, 2014
              (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

A module for interacting with an external SMT solver, using SMT-LIB 2 format.
-}

module SMT.SimpleSMT
    (
    -- * Basic Solver Interface
      Solver (..)
    , send
    , recv
    , debug
    , command
    , stop
    , Logger
    , newSolver
    , ackCommand
    , ackCommandIgnoreErr
    , simpleCommand
    , simpleCommandMaybe
    , loadFile

    -- ** S-Expressions
    , SExpr(..)
    , showSExpr, readSExprs
    , nameFromSExpr

    -- * Common SMT-LIB 2 Commands
    , Constructor (..)
    , SmtConstructor
    , ConstructorArgument (..)
    , SmtConstructorArgument
    , DataTypeDeclaration (..)
    , SmtDataTypeDeclaration
    , FunctionDeclaration (..)
    , SmtFunctionDeclaration
    , SortDeclaration (..)
    , SmtSortDeclaration
    , setLogic, setLogicMaybe
    , setOption, setOptionMaybe
    , produceUnsatCores
    , named
    , push, pushMany
    , pop, popMany
    , inNewScope
    , declare
    , declareFun
    , declareDatatype
    , declareDatatypes
    , declareSort
    , define
    , defineFun
    , assert
    , check
    , Result(..)
    , getExprs, getExpr
    , getConsts, getConst
    , getUnsatCore
    , Value(..)
    , sexprToVal

    -- * Convenience Functions for SMT-LIB2 Expressions
    , fam
    , fun
    , const

    -- ** Types
    , tInt
    , tBool
    , tReal
    , tArray
    , tBits

    -- ** Literals
    , int
    , real
    , bool
    , bvBin
    , bvHex
    , value

    -- ** Connectives
    , not
    , and
    , andMany
    , or
    , orMany
    , xor
    , implies

    -- ** If-then-else
    , ite

    -- ** Relational Predicates
    , eq
    , distinct
    , gt
    , lt
    , geq
    , leq
    , bvULt
    , bvULeq
    , bvSLt
    , bvSLeq

    -- ** Arithmetic
    , add
    , addMany
    , sub
    , neg
    , mul
    , abs
    , div
    , mod
    , divisible
    , realDiv

    -- ** Bit Vectors
    , concat
    , extract
    , bvNot
    , bvNeg
    , bvAnd
    , bvXOr
    , bvOr
    , bvAdd
    , bvSub
    , bvMul
    , bvUDiv
    , bvURem
    , bvSDiv
    , bvSRem
    , bvShl
    , bvLShr
    , bvAShr
    , signExtend
    , zeroExtend

    -- ** Arrays
    , select
    , store

    -- Quantifiers
    , forallQ
    ) where

import qualified Colog
import Control.Concurrent
    ( forkIO
    )
import qualified Control.Exception as X
import qualified Control.Monad as Monad
import Data.Bits
    ( testBit
    )
import Data.Ratio
    ( denominator
    , numerator
    , (%)
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Data.Text.Internal.Builder as Text.Builder
import qualified Data.Text.IO as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified GHC.Generics as GHC
import GHC.Stack
    ( callStack
    )
import qualified GHC.Stack as GHC
import Numeric
    ( readHex
    , showFFloat
    , showHex
    )
import Prelude hiding
    ( abs
    , and
    , concat
    , const
    , div
    , mod
    , not
    , or
    )
import qualified Prelude
import System.Exit
    ( ExitCode
    )
import System.IO
    ( Handle
    , hClose
    , hFlush
    , hPutChar
    )
import System.Process
    ( ProcessHandle
    , runInteractiveProcess
    , waitForProcess
    )
import qualified Text.Megaparsec as Parser
import Text.Read
    ( readMaybe
    )

import Kore.Debug hiding
    ( debug
    )
import qualified Kore.Logger as Logger
import SMT.AST

-- ---------------------------------------------------------------------
-- * Features

{- | Does Z3 support the @produce-assertions@ option?
 -}
featureProduceAssertions :: Bool
featureProduceAssertions =
    -- TODO (thomas.tuegel): Change this to 'True' when we drop support for
    -- older versions.
    False

-- ---------------------------------------------------------------------

-- | Results of checking for satisfiability.
data Result = Sat         -- ^ The assertions are satisfiable
            | Unsat       -- ^ The assertions are unsatisfiable
            | Unknown     -- ^ The result is inconclusive
              deriving (Eq,Show)

-- | Common values returned by SMT solvers.
data Value =  Bool  !Bool           -- ^ Boolean value
            | Int   !Integer        -- ^ Integral value
            | Real  !Rational       -- ^ Rational value
            | Bits  !Int !Integer   -- ^ Bit vector: width, value
            | Other !SExpr          -- ^ Some other value
              deriving (Eq, Show)

--------------------------------------------------------------------------------

type Logger = Logger.LogAction IO Logger.SomeEntry

-- | An interactive solver process.
data Solver = Solver
    { hIn    :: !Handle
    , hOut   :: !Handle
    , hErr   :: !Handle
    , hProc  :: !ProcessHandle
    , logger :: !Logger
    }
    deriving (GHC.Generic)

-- | Start a new solver process.
newSolver
    :: FilePath -- ^ Executable
    -> [String] -- ^ Arguments
    -> Logger   -- ^ Logger
    -> IO Solver
newSolver exe opts logger = do
    (hIn, hOut, hErr, hProc) <- runInteractiveProcess exe opts Nothing Nothing
    let solver = Solver { hIn, hOut, hErr, hProc, logger }

    _ <- forkIO $ do
        let handler X.SomeException {} = return ()
        X.handle handler $ Monad.forever $ do
            errs <- Text.hGetLine hErr
            debug solver ["stderr"] errs

    setOption solver ":print-success" "true"
    setOption solver ":produce-models" "true"
    Monad.when featureProduceAssertions
        $ setOption solver ":produce-assertions" "true"

    return solver

debug :: GHC.HasCallStack => Solver -> [Logger.Scope] -> Text -> IO ()
debug Solver { logger } scope a =
    logger Colog.<& message
  where
    message =
        Logger.SomeEntry
            $ Logger.LogMessage a Logger.Debug ("SimpleSMT" : scope) callStack

warn :: GHC.HasCallStack => Solver -> [Logger.Scope] -> Text -> IO ()
warn Solver { logger } scope a =
    logger Colog.<& message
  where
    message =
        Logger.SomeEntry
            $ Logger.LogMessage a Logger.Warning ("SimpleSMT" : scope) callStack

send :: Solver -> SExpr -> IO ()
send solver@Solver { hIn } command' = do
    debug solver ["send"] (buildText command')
    sendSExpr hIn command'
    hPutChar hIn '\n'
    hFlush hIn

recv :: Solver -> IO SExpr
recv solver@Solver { hOut } = do
    responseLines <- readResponse 0 []
    let resp = Text.unlines (reverse responseLines)
    debug solver ["recv"] resp
    readSExpr resp
  where
    {-| Reads an SMT response.

    An SMT response is either an one line atom like "sat", or an s-expression
    that may span multiple lines. To find the end of the s-expression we check
    that all parentheses are closed.
    -}
    readResponse :: Int -> [Text] -> IO [Text]
    readResponse 0 lines'
      -- If we closed all parentheses ("0" above) and we have read at least
      -- one line, then we finished reading the entire z3 response so we return.
      | Prelude.not (Prelude.null lines') = return lines'
    readResponse open lines' = do
        line <- Text.hGetLine hOut
        readResponse (open + deltaOpen line) (line : lines')

    deltaOpen :: Text -> Int
    deltaOpen line = Text.count "(" line - Text.count ")" line

command :: Solver -> SExpr -> IO SExpr
command solver c =
    traceNonErrorMonad D_SMT_command [debugArg "c" (showSExpr c)] $ do
        send solver c
        recv solver

stop :: Solver -> IO ExitCode
stop solver@Solver { hIn, hOut, hErr, hProc } = do
    send solver (List [Atom "exit"])
    ec <- waitForProcess hProc
    let handler :: X.IOException -> IO ()
        handler ex = (debug solver ["stop"] . Text.pack) (show ex)
    X.handle handler $ do
        hClose hIn
        hClose hOut
        hClose hErr
    return ec


-- | Load the contents of a file.
loadFile :: Solver -> FilePath -> IO ()
loadFile s file = do
    txt <- Text.readFile file
    case Parser.runParser (Parser.some parseSExpr) file txt of
        Left err -> fail (show err)
        Right exprs ->
            mapM_ (command s) exprs


-- | A command with no interesting result.
ackCommand :: Solver -> SExpr -> IO ()
ackCommand solver c =
  do res <- command solver c
     case res of
       Atom "success" -> return ()
       _  -> fail $ unlines
                      [ "Unexpected result from the SMT solver:"
                      , "  Command: " ++ showSExpr c
                      , "  Expected: success"
                      , "  Result: " ++ showSExpr res
                      ]

-- | A command with no interesting result.
ackCommandIgnoreErr :: Solver -> SExpr -> IO ()
ackCommandIgnoreErr proc c = do
    _ <- command proc c
    pure ()

-- | A command entirely made out of atoms, with no interesting result.
simpleCommand :: Solver -> [Text] -> IO ()
simpleCommand proc = ackCommand proc . List . map Atom

-- | Run a command and return True if successful, and False if unsupported.
-- This is useful for setting options that unsupported by some solvers, but used
-- by others.
simpleCommandMaybe :: Solver -> [Text] -> IO Bool
simpleCommandMaybe solver c =
  do let cmd = List (map Atom c)
     res <- command solver cmd
     case res of
       Atom "success"     -> return True
       Atom "unsupported" -> return False
       _                  -> fail $ unlines
                                      [ "Unexpected result from the SMT solver:"
                                      , "  Command: " ++ showSExpr cmd
                                      , "  Expected: success or unsupported"
                                      , "  Result: " ++ showSExpr res
                                      ]


-- | Set a solver option.
setOption :: Solver -> Text -> Text -> IO ()
setOption s x y = simpleCommand s [ "set-option", x, y ]

-- | Set a solver option, returning False if the option is unsupported.
setOptionMaybe :: Solver -> Text -> Text -> IO Bool
setOptionMaybe s x y = simpleCommandMaybe s [ "set-option", x, y ]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Solver -> Text -> IO ()
setLogic s x = simpleCommand s [ "set-logic", x ]


-- | Set the solver's logic, returning False if the logic is unsupported.
setLogicMaybe :: Solver -> Text -> IO Bool
setLogicMaybe s x = simpleCommandMaybe s [ "set-logic", x ]

-- | Request unsat cores.  Returns if the solver supports them.
produceUnsatCores :: Solver -> IO Bool
produceUnsatCores s = setOptionMaybe s ":produce-unsat-cores" "true"

-- | Checkpoint state.  A special case of 'pushMany'.
push :: Solver -> IO ()
push proc = pushMany proc 1

-- | Restore to last check-point.  A special case of 'popMany'.
pop :: Solver -> IO ()
pop proc = popMany proc 1

-- | Push multiple scopes.
pushMany :: Solver -> Integer -> IO ()
pushMany proc n = simpleCommand proc [ "push", Text.pack (show n) ]

-- | Pop multiple scopes.
popMany :: Solver -> Integer -> IO ()
popMany proc n = simpleCommand proc [ "pop", Text.pack (show n) ]

-- | Execute the IO action in a new solver scope (push before, pop after)
inNewScope :: Solver -> IO a -> IO a
inNewScope s m = do
    push s
    m `X.finally` pop s


-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Solver -> Text -> SExpr -> IO SExpr
declare proc f t = declareFun proc (FunctionDeclaration f [] t)

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Solver -> SmtFunctionDeclaration -> IO SExpr
declareFun proc FunctionDeclaration {name, inputSorts, resultSort} = do
    ackCommandIgnoreErr proc
        $ fun "declare-fun" [ Atom name, List inputSorts, resultSort ]
    return (const name)

declareSort :: Solver -> SmtSortDeclaration -> IO SExpr
declareSort
    proc
    SortDeclaration {name, arity}
  = do
    ackCommandIgnoreErr proc
        $ fun "declare-sort" [ Atom name, (Atom . Text.pack . show) arity ]
    pure (const name)

-- | Declare a set of ADTs
declareDatatypes
    :: Solver
    -> [ SmtDataTypeDeclaration ]
    -> IO ()
declareDatatypes proc datatypes = do
    mapM_ declareDatatypeSort datatypes
    mapM_ addSortConstructors datatypes
  where
    declareDatatypeSort :: SmtDataTypeDeclaration -> IO SExpr
    declareDatatypeSort DataTypeDeclaration { name, typeArguments } =
        declareSort
            proc
            SortDeclaration { name, arity = length typeArguments }

    addSortConstructors :: SmtDataTypeDeclaration -> IO ()
    addSortConstructors
        d@DataTypeDeclaration { constructors }
      = do
        declareConstructors d constructors
        assert proc (noJunkAxiom d constructors)
        return ()

    declareConstructors :: SmtDataTypeDeclaration -> [SmtConstructor] -> IO ()
    declareConstructors
        DataTypeDeclaration { name, typeArguments = [] }
        constructors
      =
        mapM_ (declareConstructor (Atom name)) constructors
    declareConstructors declaration constructors = (error . unlines)
        [ "Not implemented."
        , "declaration = " ++ show declaration
        , "constructors = " ++ show constructors
        ]

    declareConstructor :: SExpr -> SmtConstructor -> IO SExpr
    declareConstructor sort Constructor {name, arguments} =
        declareFun
            proc
            FunctionDeclaration
                { name
                , inputSorts = map argType arguments
                , resultSort = sort
                }

    noJunkAxiom :: SmtDataTypeDeclaration -> [SmtConstructor] -> SExpr
    noJunkAxiom
        DataTypeDeclaration { name, typeArguments = [] }
        constructors
      =
        forallQ
            -- TODO(virgil): make sure that "x" is not used in any constructors
            -- or sorts.
            [List [Atom "x", Atom name]]
            (orMany (map (builtWithConstructor "x") constructors))
    noJunkAxiom declaration constructors = (error . unlines)
        [ "Not implemented."
        , "declaration = " ++ show declaration
        , "constructors = " ++ show constructors
        ]

    builtWithConstructor :: Text -> SmtConstructor -> SExpr
    builtWithConstructor
        variable
        Constructor {name, arguments = []}
      =
        eq (Atom variable) (Atom name)
    builtWithConstructor
        variable
        Constructor {name, arguments}
      =
        existsQ
            (map mkQuantifier arguments)
            (eq (Atom variable) (fun name (map mkArg arguments)))
      where
        mkArg :: SmtConstructorArgument -> SExpr
        mkArg ConstructorArgument {name = argName} = Atom argName
        mkQuantifier :: SmtConstructorArgument -> SExpr
        mkQuantifier c@ConstructorArgument {argType} =
            List [mkArg c, argType]
  -- TODO(virgil): Currently using the code below to declare datatypes crashes
  -- z3 when testing that things can't be built out of them, e.g. things like
  -- (declare-datatypes ()
  --   (
  --       (HB_S
  --           HB_C
  --           (HB_D (HB_D1 HB_T))
  --       )
  --       (HB_T HB_E )
  --   )
  -- )
  -- (declare-fun x () HB_S )
  -- (assert (not (= x HB_C ) ) )
  -- (assert (not (= x (HB_D HB_E ) ) ) )
  -- (check-sat )
  -- will crash z3.
  --
  -- This was fixed, see https://github.com/Z3Prover/z3/issues/2217
  -- We should switch to the proper way of declaring datatypes below
  -- whenever we think we can ask people to use a version of z3 that
  -- supports them.
{-
declareDatatypes proc datatypes =
  ackCommand proc $
    -- (declare-datatypes ((δ1 k1) · · · (δn kn)) (d1 · · · dn))
    -- where δs are datatype names, ks are number of arguments
    -- and if ki is 0, then di is of the form ((CName CArgs) ..)
    fun "declare-datatypes"
      [ List $ map typeRepresentation datatypes
      , List $ map dataConstructorsRepresentation datatypes
      ]
 where
  typeRepresentation (t, args, _) =
    List [ Atom t, (Atom . Text.pack . show . length) args ]
  dataConstructorsRepresentation (_, [], cs) =
    List $ map constructorRepresentation cs
  dataConstructorsRepresentation _ = error "Unimplemented"
  constructorRepresentation (constructorName, []) = Atom constructorName
  constructorRepresentation (constructorName, constructorArgs) =
    List
      ( Atom constructorName
      : [ List [Atom s, argTy] | (s, argTy) <- constructorArgs ]
      )
-}

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatype :: Solver -> SmtDataTypeDeclaration -> IO ()
declareDatatype proc declaration = declareDatatypes proc [declaration]

-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns the defined name as a constant expression.
define :: Solver ->
          Text {- ^ New symbol -} ->
          SExpr  {- ^ Symbol type -} ->
          SExpr  {- ^ Symbol definition -} ->
          IO SExpr
define proc f = defineFun proc f []

-- | Define a function or a constant.
-- For convenience, returns an the defined name as a constant expression.
defineFun :: Solver ->
             Text           {- ^ New symbol -} ->
             [(Text,SExpr)] {- ^ Parameters, with types -} ->
             SExpr            {- ^ Type of result -} ->
             SExpr            {- ^ Definition -} ->
             IO SExpr
defineFun proc f as t e = do
    ackCommand proc $ fun "define-fun"
        [ Atom f, List [ List [const x,a] | (x,a) <- as ], t, e]
    return (const f)


buildText :: SExpr -> Text
buildText = Text.Lazy.toStrict . Text.Builder.toLazyText . buildSExpr

-- | Assume a fact.
assert :: Solver -> SExpr -> IO ()
assert proc e = ackCommand proc $ fun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Solver -> IO Result
check solver = do
    res <- command solver (List [ Atom "check-sat" ])
    case res of
        Atom "unsat"   -> return Unsat
        Atom "unknown" -> do
            Monad.when featureProduceAssertions $ do
                asserts <- command solver (List [Atom "get-assertions"])
                warn solver ["check"] (buildText asserts)
            return Unknown
        Atom "sat"     -> do
            model <- command solver (List [Atom "get-model"])
            debug solver ["check"] (buildText model)
            return Sat
        _ -> fail $ unlines
            [ "Unexpected result from the SMT solver:"
            , "  Expected: unsat, unknown, or sat"
            , "  Result: " ++ showSExpr res
            ]

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> Value
sexprToVal expr =
  case expr of
    Atom "true"                    -> Bool True
    Atom "false"                   -> Bool False
    Atom (Text.unpack -> ('#' : 'b' : ds))
      | Just n <- binLit ds         -> Bits (length ds) n
    Atom (Text.unpack -> ('#' : 'x' : ds))
      | [(n,[])] <- readHex ds      -> Bits (4 * length ds) n
    Atom (Text.unpack -> txt)
      | Just n <- readMaybe txt     -> Int n
    List [ Atom "-", x ]
      | Int a <- sexprToVal x    -> Int (negate a)
    List [ Atom "/", x, y ]
      | Int a <- sexprToVal x
      , Int b <- sexprToVal y    -> Real (a % b)
    _ -> Other expr

  where
  binLit cs = do ds <- mapM binDigit cs
                 return $ sum $ zipWith (*) (reverse ds) powers2
  powers2   = 1 : map (2 *) powers2
  binDigit '0' = Just 0
  binDigit '1' = Just 1
  binDigit _   = Nothing

-- | Get the values of some s-expressions.
-- Only valid after a 'Sat' result.
getExprs :: Solver -> [SExpr] -> IO [(SExpr, Value)]
getExprs solver vals =
  do let cmd = List [ Atom "get-value", List vals ]
     res <- command solver cmd
     case res of
       List xs -> mapM getAns xs
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Command: " ++ showSExpr cmd
                 , "  Expected: a list"
                 , "  Result: " ++ showSExpr res
                 ]
  where
  getAns expr =
    case expr of
      List [ e, v ] -> return (e, sexprToVal v)
      _             -> fail $ unlines
                            [ "Unexpected response from the SMT solver:"
                            , "  Expected: (expr val)"
                            , "  Result: " ++ showSExpr expr
                            ]

-- | Get the values of some constants in the current model.
-- A special case of 'getExprs'.
-- Only valid after a 'Sat' result.
getConsts :: Solver -> [Text] -> IO [(Text, Value)]
getConsts proc xs =
  do ans <- getExprs proc (map Atom xs)
     return [ (x,e) | (Atom x, e) <- ans ]


-- | Get the value of a single expression.
getExpr :: Solver -> SExpr -> IO Value
getExpr proc x =
  do [ (_,v) ] <- getExprs proc [x]
     return v

-- | Get the value of a single constant.
getConst :: Solver -> Text -> IO Value
getConst proc x = getExpr proc (Atom x)

-- | Returns the names of the (named) formulas involved in a contradiction.
getUnsatCore :: Solver -> IO [Text]
getUnsatCore s =
  do res <- command s $ List [ Atom "get-unsat-core" ]
     case res of
       List xs -> mapM fromAtom xs
       _       -> unexpected "a list of atoms" res
  where
  fromAtom x =
    case x of
      Atom a -> return a
      _      -> unexpected "an atom" x

  unexpected x e =
    fail $ unlines [ "Unexpected response from the SMT Solver:"
                   , "  Expected: " ++ x
                   , "  Result: " ++ showSExpr e
                   ]

--------------------------------------------------------------------------------


-- | A constant, corresponding to a family indexed by some integers.
fam :: Text -> [Integer] -> SExpr
fam f is = List (Atom "_" : Atom f : map (Atom . Text.pack . show) is)

-- | An SMT function.
fun :: Text -> [SExpr] -> SExpr
fun f [] = Atom f
fun f as = List (Atom f : as)

-- | An SMT constant.  A special case of 'fun'.
const :: Text -> SExpr
const f = fun f []


-- Types -----------------------------------------------------------------------


-- | The type of integers.
tInt :: SExpr
tInt = const "Int"

-- | The type of booleans.
tBool :: SExpr
tBool = const "Bool"

-- | The type of reals.
tReal :: SExpr
tReal = const "Real"

-- | The type of arrays.
tArray :: SExpr {- ^ Type of indexes  -} ->
          SExpr {- ^ Type of elements -} ->
          SExpr
tArray x y = fun "Array" [x,y]

-- | The type of bit vectors.
tBits :: Integer {- ^ Number of bits -} ->
         SExpr
tBits w = fam "BitVec" [w]



-- Literals --------------------------------------------------------------------

-- | Boolean literals.
bool :: Bool -> SExpr
bool b = const (if b then "true" else "false")

-- | Integer literals.
int :: Integer -> SExpr
int x | x < 0     = neg (int (negate x))
      | otherwise = Atom (Text.pack $ show x)

-- | Real (well, rational) literals.
real :: Rational -> SExpr
real x
  | toRational y == x = Atom (Text.pack $ showFFloat Nothing y "")
  | otherwise = realDiv (int (numerator x)) (int (denominator x))
  where y = fromRational x :: Double

-- | A bit vector represented in binary.
--
--     * If the value does not fit in the bits, then the bits will be increased.
--     * The width should be strictly positive.
bvBin :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvBin w v = const ("#b" <> bits)
  where
  bits =
      (Text.pack . reverse)
      [ if testBit v n then '1' else '0' | n <- [ 0 .. w - 1 ] ]

-- | A bit vector represented in hex.
--
--    * If the value does not fit in the bits, the bits will be increased to
--      the next multiple of 4 that will fit the value.
--    * If the width is not a multiple of 4, it will be rounded
--      up so that it is.
--    * The width should be strictly positive.
bvHex :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvHex w v
  | v >= 0    = const (Text.pack $ "#x" ++ padding ++ hex)
  | otherwise = bvHex w (2^w + v)
  where
  hex     = showHex v ""
  padding = replicate (Prelude.div (w + 3) 4 - length hex) '0'


-- | Render a value as an expression.  Bit-vectors are rendered in hex,
-- if their width is a multiple of 4, and in binary otherwise.
value :: Value -> SExpr
value val =
  case val of
    Bool b    -> bool b
    Int n     -> int n
    Real r    -> real r
    Bits w v
      | Prelude.mod w 4 == 0 -> bvHex w v
      | otherwise      -> bvBin w v
    Other o   -> o

-- Connectives -----------------------------------------------------------------

-- | Logical negation.
not :: SExpr -> SExpr
not p = fun "not" [p]

-- | Conjunction.
and :: SExpr -> SExpr -> SExpr
and p q = fun "and" [p,q]

andMany :: [SExpr] -> SExpr
andMany xs = if null xs then bool True else fun "and" xs

-- | Disjunction.
or :: SExpr -> SExpr -> SExpr
or p q = fun "or" [p,q]

orMany :: [SExpr] -> SExpr
orMany xs = if null xs then bool False else fun "or" xs

-- | Exclusive-or.
xor :: SExpr -> SExpr -> SExpr
xor p q = fun "xor" [p,q]

-- | Implication.
implies :: SExpr -> SExpr -> SExpr
implies p q = fun "=>" [p,q]


-- If-then-else ----------------------------------------------------------------

-- | If-then-else.  This is polymorphic and can be used to construct any term.
ite :: SExpr -> SExpr -> SExpr -> SExpr
ite x y z = fun "ite" [x,y,z]




-- Relations -------------------------------------------------------------------

-- | Equality.
eq :: SExpr -> SExpr -> SExpr
eq x y = fun "=" [x,y]

distinct :: [SExpr] -> SExpr
distinct xs = if null xs then bool True else fun "distinct" xs

-- | Greater-then
gt :: SExpr -> SExpr -> SExpr
gt x y = fun ">" [x,y]

-- | Less-then.
lt :: SExpr -> SExpr -> SExpr
lt x y = fun "<" [x,y]

-- | Greater-than-or-equal-to.
geq :: SExpr -> SExpr -> SExpr
geq x y = fun ">=" [x,y]

-- | Less-than-or-equal-to.
leq :: SExpr -> SExpr -> SExpr
leq x y = fun "<=" [x,y]

-- | Unsigned less-than on bit-vectors.
bvULt :: SExpr -> SExpr -> SExpr
bvULt x y = fun "bvult" [x,y]

-- | Unsigned less-than-or-equal on bit-vectors.
bvULeq :: SExpr -> SExpr -> SExpr
bvULeq x y = fun "bvule" [x,y]

-- | Signed less-than on bit-vectors.
bvSLt :: SExpr -> SExpr -> SExpr
bvSLt x y = fun "bvslt" [x,y]

-- | Signed less-than-or-equal on bit-vectors.
bvSLeq :: SExpr -> SExpr -> SExpr
bvSLeq x y = fun "bvsle" [x,y]




-- | Addition.
-- See also 'bvAdd'
add :: SExpr -> SExpr -> SExpr
add x y = fun "+" [x,y]

addMany :: [SExpr] -> SExpr
addMany xs = if null xs then int 0 else fun "+" xs

-- | Subtraction.
sub :: SExpr -> SExpr -> SExpr
sub x y = fun "-" [x,y]

-- | Arithmetic negation for integers and reals.
-- See also 'bvNeg'.
neg :: SExpr -> SExpr
neg x = fun "-" [x]

-- | Multiplication.
mul :: SExpr -> SExpr -> SExpr
mul x y = fun "*" [x,y]

-- | Absolute value.
abs :: SExpr -> SExpr
abs x = fun "abs" [x]

-- | Integer division.
div :: SExpr -> SExpr -> SExpr
div x y = fun "div" [x,y]

-- | Modulus.
mod :: SExpr -> SExpr -> SExpr
mod x y = fun "mod" [x,y]

-- | Is the number divisible by the given constant.
divisible :: SExpr -> Integer -> SExpr
divisible x n = List [ fam "divisible" [n], x ]

-- | Division of real numbers.
realDiv :: SExpr -> SExpr -> SExpr
realDiv x y = fun "/" [x,y]

-- | Bit vector concatenation.
concat :: SExpr -> SExpr -> SExpr
concat x y = fun "concat" [x,y]

-- | Extend to the signed equivalent bitvector by @i@ bits
signExtend :: Integer -> SExpr -> SExpr
signExtend i x = List [ fam "sign_extend" [i], x ]

-- | Extend with zeros to the unsigned equivalent bitvector
-- by @i@ bits
zeroExtend :: Integer -> SExpr -> SExpr
zeroExtend i x = List [ fam "zero_extend" [i], x ]

-- | Extract a sub-sequence of a bit vector.
extract :: SExpr -> Integer -> Integer -> SExpr
extract x y z = List [ fam "extract" [y,z], x ]

-- | Bitwise negation.
bvNot :: SExpr -> SExpr
bvNot x = fun "bvnot" [x]

-- | Bitwise conjuction.
bvAnd :: SExpr -> SExpr -> SExpr
bvAnd x y = fun "bvand" [x,y]

-- | Bitwise disjunction.
bvOr :: SExpr -> SExpr -> SExpr
bvOr x y = fun "bvor" [x,y]

-- | Bitwise exclusive or.
bvXOr :: SExpr -> SExpr -> SExpr
bvXOr x y = fun "bvxor" [x,y]

-- | Bit vector arithmetic negation.
bvNeg :: SExpr -> SExpr
bvNeg x = fun "bvneg" [x]

-- | Addition of bit vectors.
bvAdd :: SExpr -> SExpr -> SExpr
bvAdd x y = fun "bvadd" [x,y]

-- | Subtraction of bit vectors.
bvSub :: SExpr -> SExpr -> SExpr
bvSub x y = fun "bvsub" [x,y]



-- | Multiplication of bit vectors.
bvMul :: SExpr -> SExpr -> SExpr
bvMul x y = fun "bvmul" [x,y]

-- | Bit vector unsigned division.
bvUDiv :: SExpr -> SExpr -> SExpr
bvUDiv x y = fun "bvudiv" [x,y]

-- | Bit vector unsigned reminder.
bvURem :: SExpr -> SExpr -> SExpr
bvURem x y = fun "bvurem" [x,y]

-- | Bit vector signed division.
bvSDiv :: SExpr -> SExpr -> SExpr
bvSDiv x y = fun "bvsdiv" [x,y]

-- | Bit vector signed reminder.
bvSRem :: SExpr -> SExpr -> SExpr
bvSRem x y = fun "bvsrem" [x,y]




-- | Shift left.
bvShl :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvShl x y = fun "bvshl" [x,y]

-- | Logical shift right.
bvLShr :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvLShr x y = fun "bvlshr" [x,y]

-- | Arithemti shift right (copies most significant bit).
bvAShr :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvAShr x y = fun "bvashr" [x,y]


-- | Get an elemeent of an array.
select :: SExpr {- ^ array -} -> SExpr {- ^ index -} -> SExpr
select x y = fun "select" [x,y]

-- | Update an array
store :: SExpr {- ^ array -}     ->
         SExpr {- ^ index -}     ->
         SExpr {- ^ new value -} ->
         SExpr
store x y z = fun "store" [x,y,z]

-- | Quantifiers: forall
--
-- Each variable is an (variable-name variable-type) sexpression.
forallQ :: [SExpr] -> SExpr -> SExpr
forallQ variables expression =
    fun "forall" [List variables, expression]

-- | Quantifiers: exists
--
-- Each variable is an (variable-name variable-type) sexpression.
existsQ :: [SExpr] -> SExpr -> SExpr
existsQ variables expression =
    fun "exists" [List variables, expression]

--------------------------------------------------------------------------------
-- Attributes

named :: Text -> SExpr -> SExpr
named x e = fun "!" [e, Atom ":named", Atom x ]


--------------------------------------------------------------------------------

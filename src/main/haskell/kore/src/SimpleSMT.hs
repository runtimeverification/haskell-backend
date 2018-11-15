{-|
Module      : SimpleSMT
Description : Simple SMT-LIB 2 interface
Copyright   : (c) Iavor S. Diatchki, 2014
              (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

A module for interacting with an external SMT solver, using SMT-LIB 2 format.
-}

{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE RecordWildCards #-}

module SimpleSMT
    (
    -- * Basic Solver Interface
      Solver(..)
    , newSolver
    , ackCommand
    , simpleCommand
    , simpleCommandMaybe
    , loadFile

    -- ** S-Expressions
    , SExpr(..)
    , showsSExpr, ppSExpr, readSExpr

    -- ** Logging and Debugging
    , Logger(..)
    , newLogger
    , withLogLevel
    , logMessageAt
    , logIndented

    -- * Common SMT-LIB 2 Commands
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
    ) where

import           Control.Concurrent
                 ( forkIO )
import qualified Control.Exception as X
import           Control.Monad
                 ( forever, when )
import           Data.Bits
                 ( testBit )
import           Data.Char
                 ( isSpace )
import           Data.IORef
                 ( atomicModifyIORef, modifyIORef', newIORef, readIORef,
                 writeIORef )
import           Data.List
                 ( intersperse, unfoldr )
import           Data.Ratio
                 ( denominator, numerator, (%) )
import           Numeric
                 ( readHex, showFFloat, showHex )
import           Prelude hiding
                 ( abs, and, concat, const, div, mod, not, or )
import qualified Prelude as P
import           System.Exit
                 ( ExitCode )
import           System.IO
                 ( hClose, hFlush, hGetContents, hGetLine, hPutStrLn, stdout )
import           System.Process
                 ( runInteractiveProcess, waitForProcess )
import           Text.Read
                 ( readMaybe )


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
              deriving (Eq,Show)

-- | S-expressions. These are the basic format for SmtLib-2.
data SExpr  = Atom String
            | List [SExpr]
              deriving (Eq, Ord, Show)

-- | Show an s-expression.
showsSExpr :: SExpr -> ShowS
showsSExpr ex =
  case ex of
    Atom x  -> showString x
    List es -> showChar '(' .
                foldr (\e m -> showsSExpr e . showChar ' ' . m)
                (showChar ')') es


-- | Show an S-expression in a somewhat readbale fashion.
ppSExpr :: SExpr -> ShowS
ppSExpr = go 0
  where
  tab n = showString (replicate n ' ')
  many  = foldr (.) id

  new n e = showChar '\n' . tab n . go n e

  small :: Int -> [SExpr] -> Maybe [ShowS]
  small n es =
    case es of
      [] -> Just []
      e : more
        | n <= 0 -> Nothing
        | otherwise -> case e of
                         Atom x -> (showString x :) <$> small (n-1) more
                         _      -> Nothing

  go :: Int -> SExpr -> ShowS
  go n ex =
    case ex of
      Atom x        -> showString x
      List es
        | Just fs <- small 5 es ->
          showChar '(' . many (intersperse (showChar ' ') fs) . showChar ')'

      List (Atom x : es) -> showString "(" . showString x .
                                many (map (new (n+3)) es) . showString ")"

      List es -> showString "(" . many (map (new (n+2)) es) . showString ")"

-- | Parse an s-expression.
readSExpr :: String -> Maybe (SExpr, String)
readSExpr (c : more) | isSpace c = readSExpr more
readSExpr (';' : more) = readSExpr $ drop 1 $ dropWhile (/= '\n') more
readSExpr ('(' : more) = do (xs,more1) <- list more
                            return (List xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- readSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
readSExpr txt     = case break end txt of
                       (as,bs) | P.not (null as) -> Just (Atom as, bs)
                       _ -> Nothing
  where end x = x == ')' || isSpace x


--------------------------------------------------------------------------------

-- | An interactive solver process.
data Solver = Solver
  { command   :: SExpr -> IO SExpr
    -- ^ Send a command to the solver.

  , stop :: IO ExitCode
    -- ^ Terminate the solver.
  }


-- | Start a new solver process.
newSolver :: String       {- ^ Executable -}            ->
             [String]     {- ^ Arguments -}             ->
             Maybe Logger {- ^ Optional logging here -} ->
             IO Solver
newSolver exe opts mbLog =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     let info a = case mbLog of
                    Nothing -> return ()
                    Just l  -> logMessage l a

     _ <- forkIO $ forever (do errs <- hGetLine hErr
                               info ("[stderr] " ++ errs))
                    `X.catch` \X.SomeException {} -> return ()

     getResponse <-
       do txt <- hGetContents hOut                  -- Read *all* output
          ref <- newIORef (unfoldr readSExpr txt)  -- Parse, and store result
          return $ atomicModifyIORef ref $ \xs ->
                      case xs of
                        []     -> (xs, Nothing)
                        y : ys -> (ys, Just y)

     let cmd c = do let txt = showsSExpr c ""
                    info ("[send->] " ++ txt)
                    hPutStrLn hIn txt
                    hFlush hIn

         command c =
           do cmd c
              mb <- getResponse
              case mb of
                Just res -> do info ("[<-recv] " ++ showsSExpr res "")
                               return res
                Nothing  -> fail "Missing response from solver"

         stop =
           do cmd (List [Atom "exit"])
              ec <- waitForProcess h
              X.catch (do hClose hIn
                          hClose hOut
                          hClose hErr)
                      (\ex -> info (show (ex::X.IOException)))
              return ec

         solver = Solver { .. }

     setOption solver ":print-success" "true"
     setOption solver ":produce-models" "true"

     return solver


-- | Load the contents of a file.
loadFile :: Solver -> FilePath -> IO ()
loadFile s file = loadString s =<< readFile file

-- | Load a raw SMT string.
loadString :: Solver -> String -> IO ()
loadString s str = go (dropComments str)
  where
  go txt
    | all isSpace txt = return ()
    | otherwise =
      case readSExpr txt of
        Just (e,rest) -> command s e >> go rest
        Nothing       -> fail $ unlines [ "Failed to parse SMT file."
                                        , txt
                                        ]

  dropComments = unlines . map dropComment . lines
  dropComment xs = case break (== ';') xs of
                     (as,_:_) -> as
                     _ -> xs




-- | A command with no interesting result.
ackCommand :: Solver -> SExpr -> IO ()
ackCommand proc c =
  do res <- command proc c
     case res of
       Atom "success" -> return ()
       _  -> fail $ unlines
                      [ "Unexpected result from the SMT solver:"
                      , "  Expected: success"
                      , "  Result: " ++ showsSExpr res ""
                      ]

-- | A command entirely made out of atoms, with no interesting result.
simpleCommand :: Solver -> [String] -> IO ()
simpleCommand proc = ackCommand proc . List . map Atom

-- | Run a command and return True if successful, and False if unsupported.
-- This is useful for setting options that unsupported by some solvers, but used
-- by others.
simpleCommandMaybe :: Solver -> [String] -> IO Bool
simpleCommandMaybe proc c =
  do res <- command proc (List (map Atom c))
     case res of
       Atom "success"     -> return True
       Atom "unsupported" -> return False
       _                  -> fail $ unlines
                                      [ "Unexpected result from the SMT solver:"
                                      , "  Expected: success or unsupported"
                                      , "  Result: " ++ showsSExpr res ""
                                      ]


-- | Set a solver option.
setOption :: Solver -> String -> String -> IO ()
setOption s x y = simpleCommand s [ "set-option", x, y ]

-- | Set a solver option, returning False if the option is unsupported.
setOptionMaybe :: Solver -> String -> String -> IO Bool
setOptionMaybe s x y = simpleCommandMaybe s [ "set-option", x, y ]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Solver -> String -> IO ()
setLogic s x = simpleCommand s [ "set-logic", x ]


-- | Set the solver's logic, returning False if the logic is unsupported.
setLogicMaybe :: Solver -> String -> IO Bool
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
pushMany proc n = simpleCommand proc [ "push", show n ]

-- | Pop multiple scopes.
popMany :: Solver -> Integer -> IO ()
popMany proc n = simpleCommand proc [ "pop", show n ]

-- | Execute the IO action in a new solver scope (push before, pop after)
inNewScope :: Solver -> IO a -> IO a
inNewScope s m =
  do push s
     m `X.finally` pop s



-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Solver -> String -> SExpr -> IO SExpr
declare proc f t = declareFun proc f [] t

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Solver -> String -> [SExpr] -> SExpr -> IO SExpr
declareFun proc f as r =
  do ackCommand proc $ fun "declare-fun" [ Atom f, List as, r ]
     return (const f)

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatype ::
  Solver ->
  String {- ^ datatype name -} ->
  [String] {- ^ sort parameters -} ->
  [(String, [(String, SExpr)])] {- ^ constructors -} ->
  IO ()
declareDatatype proc t [] cs =
  ackCommand proc $
    fun "declare-datatype" $
      [ Atom t
      , List [ List (Atom c : [ List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs ]
      ]
declareDatatype proc t ps cs =
  ackCommand proc $
    fun "declare-datatype" $
      [ Atom t
      , fun "par" $
          [ List (map Atom ps)
          , List [ List (Atom c : [ List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs ]
          ]
      ]


-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns the defined name as a constant expression.
define :: Solver ->
          String {- ^ New symbol -} ->
          SExpr  {- ^ Symbol type -} ->
          SExpr  {- ^ Symbol definition -} ->
          IO SExpr
define proc f t e = defineFun proc f [] t e

-- | Define a function or a constant.
-- For convenience, returns an the defined name as a constant expression.
defineFun :: Solver ->
             String           {- ^ New symbol -} ->
             [(String,SExpr)] {- ^ Parameters, with types -} ->
             SExpr            {- ^ Type of result -} ->
             SExpr            {- ^ Definition -} ->
             IO SExpr
defineFun proc f as t e =
  do ackCommand proc $ fun "define-fun"
                     $ [ Atom f, List [ List [const x,a] | (x,a) <- as ], t, e]
     return (const f)



-- | Assume a fact.
assert :: Solver -> SExpr -> IO ()
assert proc e = ackCommand proc $ fun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Solver -> IO Result
check proc =
  do res <- command proc (List [ Atom "check-sat" ])
     case res of
       Atom "unsat"   -> return Unsat
       Atom "unknown" -> return Unknown
       Atom "sat"     -> return Sat
       _ -> fail $ unlines
              [ "Unexpected result from the SMT solver:"
              , "  Expected: unsat, unknown, or sat"
              , "  Result: " ++ showsSExpr res ""
              ]

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> Value
sexprToVal expr =
  case expr of
    Atom "true"                    -> Bool True
    Atom "false"                   -> Bool False
    Atom ('#' : 'b' : ds)
      | Just n <- binLit ds         -> Bits (length ds) n
    Atom ('#' : 'x' : ds)
      | [(n,[])] <- readHex ds      -> Bits (4 * length ds) n
    Atom txt
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
getExprs proc vals =
  do res <- command proc $ List [ Atom "get-value", List vals ]
     case res of
       List xs -> mapM getAns xs
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Exptected: a list"
                 , "  Result: " ++ showsSExpr res ""
                 ]
  where
  getAns expr =
    case expr of
      List [ e, v ] -> return (e, sexprToVal v)
      _             -> fail $ unlines
                            [ "Unexpected response from the SMT solver:"
                            , "  Expected: (expr val)"
                            , "  Result: " ++ showsSExpr expr ""
                            ]

-- | Get the values of some constants in the current model.
-- A special case of 'getExprs'.
-- Only valid after a 'Sat' result.
getConsts :: Solver -> [String] -> IO [(String, Value)]
getConsts proc xs =
  do ans <- getExprs proc (map Atom xs)
     return [ (x,e) | (Atom x, e) <- ans ]


-- | Get the value of a single expression.
getExpr :: Solver -> SExpr -> IO Value
getExpr proc x =
  do [ (_,v) ] <- getExprs proc [x]
     return v

-- | Get the value of a single constant.
getConst :: Solver -> String -> IO Value
getConst proc x = getExpr proc (Atom x)

-- | Returns the names of the (named) formulas involved in a contradiction.
getUnsatCore :: Solver -> IO [String]
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
                   , "  Result: " ++ showsSExpr e ""
                   ]

--------------------------------------------------------------------------------


-- | A constant, corresponding to a family indexed by some integers.
fam :: String -> [Integer] -> SExpr
fam f is = List (Atom "_" : Atom f : map (Atom . show) is)

-- | An SMT function.
fun :: String -> [SExpr] -> SExpr
fun f [] = Atom f
fun f as = List (Atom f : as)

-- | An SMT constant.  A special case of 'fun'.
const :: String -> SExpr
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
      | otherwise = Atom (show x)

-- | Real (well, rational) literals.
real :: Rational -> SExpr
real x
  | toRational y == x = Atom (showFFloat Nothing y "")
  | otherwise = realDiv (int (numerator x)) (int (denominator x))
  where y = fromRational x :: Double

-- | A bit vector represented in binary.
--
--     * If the value does not fit in the bits, then the bits will be increased.
--     * The width should be strictly positive.
bvBin :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvBin w v = const ("#b" ++ bits)
  where
  bits = reverse [ if testBit v n then '1' else '0' | n <- [ 0 .. w - 1 ] ]

-- | A bit vector represented in hex.
--
--    * If the value does not fit in the bits, the bits will be increased to
--      the next multiple of 4 that will fit the value.
--    * If the width is not a multiple of 4, it will be rounded
--      up so that it is.
--    * The width should be strictly positive.
bvHex :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvHex w v
  | v >= 0    = const ("#x" ++ padding ++ hex)
  | otherwise = bvHex w (2^w + v)
  where
  hex     = showHex v ""
  padding = replicate (P.div (w + 3) 4 - length hex) '0'


-- | Render a value as an expression.  Bit-vectors are rendered in hex,
-- if their width is a multiple of 4, and in binary otherwise.
value :: Value -> SExpr
value val =
  case val of
    Bool b    -> bool b
    Int n     -> int n
    Real r    -> real r
    Bits w v | P.mod w 4 == 0 -> bvHex w v
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


--------------------------------------------------------------------------------
-- Attributes

named :: String -> SExpr -> SExpr
named x e = fun "!" [e, Atom ":named", Atom x ]


--------------------------------------------------------------------------------

-- | Log messages with minimal formatting. Mostly for debugging.
data Logger = Logger
  { logMessage :: String -> IO ()
    -- ^ Log a message.

  , logLevel   :: IO Int

  , logSetLevel:: Int -> IO ()

  , logTab     :: IO ()
    -- ^ Increase indentation.

  , logUntab   :: IO ()
    -- ^ Decrease indentation.
  }

-- | Run an IO action with the logger set to a specific level, restoring it when
-- done.
withLogLevel :: Logger -> Int -> IO a -> IO a
withLogLevel Logger { .. } l m =
  do l0 <- logLevel
     X.bracket_ (logSetLevel l) (logSetLevel l0) m

logIndented :: Logger -> IO a -> IO a
logIndented Logger { .. } = X.bracket_ logTab logUntab

-- | Log a message at a specific log level.
logMessageAt :: Logger -> Int -> String -> IO ()
logMessageAt logger l msg = withLogLevel logger l (logMessage logger msg)

-- | A simple stdout logger.  Shows only messages logged at a level that is
-- greater than or equal to the passed level.
newLogger :: Int -> IO Logger
newLogger l =
  do tab <- newIORef 0
     lev <- newIORef 0
     let logLevel    = readIORef lev
         logSetLevel = writeIORef lev

         shouldLog m =
           do cl <- logLevel
              when (cl >= l) m

         logMessage x = shouldLog $
           do t <- readIORef tab
              putStr $ unlines [ replicate t ' ' ++ line | line <- lines x ]
              hFlush stdout

         logTab   = shouldLog (modifyIORef' tab (+ 2))
         logUntab = shouldLog (modifyIORef' tab (subtract 2))
     return Logger { .. }

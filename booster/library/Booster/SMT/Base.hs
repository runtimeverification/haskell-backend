{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.SMT.Base (
    module Booster.SMT.Base,
) where

import Control.DeepSeq (NFData (..))
import Data.ByteString.Char8 qualified as BS
import Data.Data (Data)
import Data.Hashable (Hashable)
import Data.String
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)

{- SMT lib 2 commands and responses

  Follows smtlib2 v2.6 grammar, see
  https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf

  Commands are grouped into declarations (carry data, no response),
  queries (carry no data, response is important), and session control.
-}

newtype SMTId = SMTId {bs :: BS.ByteString}
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving newtype (IsString, NFData, Hashable)

data SMTSort
    = SimpleSMTSort SMTId
    | SMTSort SMTId [SMTSort]
    deriving stock (Eq, Ord, Show)

data SExpr -- SMTTerm
    = Atom SMTId
    | List [SExpr]
    deriving stock (Eq, Ord, Show)
    deriving stock (Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

data SMTCommand
    = Declare DeclareCommand -- no response required
    | Query QueryCommand -- response essential
    | Control ControlCommand
    deriving stock (Eq, Ord, Show)

data DeclareCommand
    = Assert SExpr
    | DeclareConst SMTId SMTSort
    | DeclareSort SMTId Int
    | DeclareFunc SMTId [SMTSort] SMTSort
    deriving stock (Eq, Ord, Show)

data ControlCommand
    = Push -- Int
    | Pop -- Int
    | Exit
    deriving stock (Eq, Ord, Show)

data QueryCommand
    = CheckSat
    | GetValue [SExpr] -- for get-model
    deriving stock (Eq, Ord, Show)

data Response
    = Success -- for command_
    | Sat
    | Unsat
    | Unknown
    | Values [(SExpr, Value)]
    | Error BS.ByteString
    deriving stock (Eq, Ord, Show)

-- Common values returned by SMT solvers.
data Value
    = Bool !Bool
    | Int !Integer
    | Other !SExpr
    deriving stock (Eq, Ord, Show)

----------------------------------------
-- well-known arithmetic functions, implemented through Num

instance Num SExpr where
    a + b = List [Atom "+", a, b]
    a - b = List [Atom "-", a, b]
    a * b = List [Atom "*", a, b]
    negate a = List [Atom "-", a]
    abs a = List [Atom "abs", a]
    signum _ = error "signum @SExpr not implemented"
    fromInteger n
        | n >= 0 = Atom . SMTId . BS.pack $ show n
        | otherwise = List [Atom "-", fromInteger (negate n)]

smtInt, smtBool :: SMTSort
smtInt = SimpleSMTSort "Int"
smtBool = SimpleSMTSort "Bool"

-- well-known combinators
eq, neq, le, leq, gr, geq, implies, and :: SExpr -> SExpr -> SExpr
eq = mkOp "="
neq = mkOp "distinct"
le = mkOp "<"
leq = mkOp "<="
gr = mkOp ">"
geq = mkOp ">="
implies = mkOp "=>"
and = mkOp "and"

mkOp :: BS.ByteString -> SExpr -> SExpr -> SExpr
mkOp opString a b = List [Atom $ SMTId opString, a, b]

smtnot :: SExpr -> SExpr
smtnot x = List [Atom "not", x]

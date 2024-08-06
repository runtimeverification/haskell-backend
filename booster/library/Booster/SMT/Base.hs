{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveFunctor #-}

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
import Data.Text (Text)
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

-- DeclareCommands carry a comment which is printed into the
-- transcript (unless it is empty) to refer to the K world
data DeclareCommand
    = Assert BS.ByteString SExpr
    | DeclareConst BS.ByteString SMTId SMTSort
    | DeclareSort BS.ByteString SMTId Int
    | DeclareFunc BS.ByteString SMTId [SMTSort] SMTSort
    deriving stock (Eq, Ord, Show)

getComment :: DeclareCommand -> BS.ByteString
getComment (Assert c _) = c
getComment (DeclareConst c _ _) = c
getComment (DeclareSort c _ _) = c
getComment (DeclareFunc c _ _ _) = c

data ControlCommand
    = Push -- Int
    | Pop -- Int
    | SetTimeout Int
    | Exit
    deriving stock (Eq, Ord, Show)

data QueryCommand
    = CheckSat
    | GetValue [SExpr] -- for get-model
    | GetReasonUnknown
    deriving stock (Eq, Ord, Show)

data Response' reason
    = Success -- for command_
    | Sat
    | Unsat
    | Unknown reason
    | Values [(SExpr, Value)]
    | Error BS.ByteString
    deriving stock (Eq, Ord, Show, Functor)

type Response = Response' Text
type ResponseUnresolved = Response' (Maybe Text)

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

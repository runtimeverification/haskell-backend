{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

{- |
Description: A test checking a proof of 1+1=2 in the mimimal proof system

This test uses its own version of the proof system because some
additional assumptions had to be added as proof rules, and its own
AST because the proof was done assuming the forall quantifier is primitive.
-}
module Test.Logic.Matching.Rules.OnePlusOne where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Applicative
import           Control.Monad
                 ( foldM )
import           Control.Monad.State.Strict
import qualified Data.ByteString.Lazy as L
import           Data.Data
import           Data.Functor.Foldable
                 ( Fix (Fix) )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Tree as Tree
import           Data.Void
                 ( Void )
import           Data.Word
import           GHC.Generics
import           Prelude hiding
                 ( all, and, lines, not, pred, succ )
import           Text.Megaparsec
                 ( Parsec, eof, parse, parseErrorPretty )
import           Text.Megaparsec.Byte
import qualified Text.Megaparsec.Byte.Lexer as Lexer

import Logic.Matching.Signature.Simple
import Logic.Proof.Hilbert as HilbertProof
       ( Proof (..), add, derive, emptyProof )

import qualified Paths
import qualified Test.Logic.Matching.Rules.OnePlusOne.Pattern as AST
import           Test.Logic.Matching.Rules.OnePlusOne.Rules
                 ( MLRule (..), MLRuleSig, SubstitutedVariable (..),
                 SubstitutingVariable (..), transformRule )

-- START code extracted by Coq
data Nat =
   O
 | S Nat
  deriving (Read,Show,Eq,Generic,Data)

data Formula =
   Plus Formula Formula
 | Succ Formula
 | Zero
 | Not Formula
 | And Formula Formula
 | Var Nat
 | All Nat Formula
 | Defined Formula
  deriving (Read,Show,Eq,Generic,Data)

data Ctx =
   SuccC
 | PlusLC Formula
 | PlusRC Formula
 | DefinedC
  deriving (Read,Show,Eq,Generic,Data)

data Ctx_path =
   Path_nil
 | Path_cons Ctx Ctx_path
  deriving (Read,Show,Eq,Generic,Data)

data Simple_rule =
   Rule_mp Simple_proof Simple_proof
 | Rule_frame Ctx Simple_proof
 | Rule_gen Nat Simple_proof
 | Rule_use_hyp Nat
 | Ax_propositional1 Formula Formula
 | Ax_propositional2 Formula Formula Formula
 | Ax_propositional3 Formula Formula
 | Ax_varSubst Nat Nat Formula Formula
 | Ax_allImp Nat Formula Formula
 | Ax_out_ex Ctx Nat Formula
 | Ax_out_or Ctx Formula Formula
 | Ax_existence Nat
 | Ax_singvar Ctx_path Ctx_path Nat Formula
 {- Additional rules used in the Coq proof.
    Some can be hypotheses of the final proof, but
    most are axiom schemes. -}
 | Ax_definedness -- This becomes a hypothesis in the output proof
 -- proj1 proves A /\ B -> A
 | Ax_proj1 Formula Formula
 -- proj2 proves A /\ B -> B
 | Ax_proj2 Formula Formula
 -- and_intro proves A -> B -> A /\ B
 | Ax_and_intro Formula Formula
 -- or_elim proves (A -> C) -> (B -> C) -> (A \/ B -> C)
 | Ax_or_elim Formula Formula Formula
 -- or_intro1 proves A -> A \/ B
 | Ax_or_intro1 Formula Formula
 -- or_intro1 proves B -> A \/ B
 | Ax_or_intro2 Formula Formula
 -- zero_functional is Ex 1 . 1 = zero()
 -- This becomes a hypothesis
 -- recall variables are just numbers.
 | Ax_zero_functional
 -- succ_functional is Ex 1 . 1 = succ(0)
 -- This becomes a hypothesis
 | Ax_succ_functional
  deriving (Read,Show,Eq,Generic,Data)

data Simple_proof =
   Conclusion Formula Simple_rule
  deriving (Read,Show,Eq,Generic,Data)
-- END code extracted by Coq.

type Parser = Parsec Void L.ByteString

{-
  This parser accepts the same input as the Read instance,
  but Read takes over a minute to load the proof and
  this Megaparsec parser is about 10x faster.
-}
lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme space

symbol :: L.ByteString -> Parser L.ByteString
symbol s = lexeme (string s)

fromChar :: Char -> Word8
fromChar c = fromIntegral (fromEnum c)

parens :: Parser a -> Parser a
parens p = do
    _ <- char (fromChar '(')
    result <- p
    _ <- lexeme (char (fromChar ')'))
    return result


pNat :: Parser Nat
pNat = parens (S <$ symbol "S" <*> pNat) <|> O <$ symbol "O"

pFormula :: Parser Formula
pFormula = atoms <|> parens phrases
  where
    atoms = Zero <$ symbol "Zero"
    phrases = Plus <$ symbol "Plus" <*> pFormula <*> pFormula
        <|> Succ <$ symbol "Succ" <*> pFormula
        <|> Not <$ symbol "Not" <*> pFormula
        <|> And <$ symbol "And" <*> pFormula <*> pFormula
        <|> Var <$ symbol "Var" <*> pNat
        <|> All <$ symbol "All" <*> pNat <*> pFormula
        <|> Defined <$ symbol "Defined" <*> pFormula

pCtx :: Parser Ctx
pCtx = atoms <|> parens phrases
  where
    atoms = SuccC <$ symbol "SuccC"
        <|> DefinedC <$ symbol "DefinedC"
    phrases = PlusLC <$ symbol "PlusLC" <*> pFormula
        <|> PlusRC <$ symbol "PlusRC" <*> pFormula

pCtx_path :: Parser Ctx_path
pCtx_path =
   Path_nil <$ symbol "Path_nil"
   <|> parens (Path_cons <$ symbol "Path_cons" <*> pCtx <*> pCtx_path)

pSimple_rule :: Parser Simple_rule
pSimple_rule = atoms <|> parens phrases
  where
    atoms = Ax_definedness <$ symbol "Ax_definedness"
        <|> Ax_zero_functional <$ symbol "Ax_zero_functional"
        <|> Ax_succ_functional <$ symbol "Ax_succ_functional"
    phrases = Rule_mp <$ symbol "Rule_mp" <*> pSimple_proof <*> pSimple_proof
        <|> Rule_frame <$ symbol "Rule_frame" <*> pCtx <*> pSimple_proof
        <|> Rule_gen <$ symbol "Rule_gen" <*> pNat <*> pSimple_proof
        <|> Rule_use_hyp <$ symbol "Rule_use_hyp" <*> pNat
        <|> Ax_propositional1 <$ symbol "Ax_propositional1" <*> pFormula <*> pFormula
        <|> Ax_propositional2 <$ symbol "Ax_propositional2" <*> pFormula <*> pFormula <*> pFormula
        <|> Ax_propositional3 <$ symbol "Ax_propositional3" <*> pFormula <*> pFormula
        <|> Ax_varSubst <$ symbol "Ax_varSubst" <*> pNat <*> pNat <*> pFormula <*> pFormula
        <|> Ax_allImp <$ symbol "Ax_allImp" <*> pNat <*> pFormula <*> pFormula
        <|> Ax_out_ex <$ symbol "Ax_out_ex" <*> pCtx <*> pNat <*> pFormula
        <|> Ax_out_or <$ symbol "Ax_out_or" <*> pCtx <*> pFormula <*> pFormula
        <|> Ax_existence <$ symbol "Ax_existence" <*> pNat
        <|> Ax_singvar <$ symbol "Ax_singvar" <*> pCtx_path <*> pCtx_path <*> pNat <*> pFormula
        <|> Ax_proj1 <$ symbol "Ax_proj1" <*> pFormula <*> pFormula
        <|> Ax_proj2 <$ symbol "Ax_proj2" <*> pFormula <*> pFormula
        <|> Ax_and_intro <$ symbol "Ax_and_intro" <*> pFormula <*> pFormula
        <|> Ax_or_elim <$ symbol "Ax_or_elim" <*> pFormula <*> pFormula <*> pFormula
        <|> Ax_or_intro1 <$ symbol "Ax_or_intro1" <*> pFormula <*> pFormula
        <|> Ax_or_intro2 <$ symbol "Ax_or_intro2" <*> pFormula <*> pFormula

pSimple_proof, pSimple_proof' :: Parser Simple_proof
pSimple_proof' = Conclusion <$ symbol "Conclusion" <*> pFormula <*> pSimple_rule
pSimple_proof = parens pSimple_proof'


nat2Int :: Num i => Nat -> i
nat2Int n = go 0 n
  where go !x O      = x
        go !x (S n') = go (x+1) n'

ctxRule :: (Text -> Int -> a) -> Ctx -> a
ctxRule f SuccC      = f "succ" 0
ctxRule f (PlusLC _) = f "plus" 0
ctxRule f (PlusRC _) = f "plus" 1
ctxRule f DefinedC   = f "defined" 0

convertCtxRule :: Ctx -> ix -> MLRule sort Text var term ix
convertCtxRule SuccC      = Framing "succ" 0
convertCtxRule (PlusLC _) = Framing "plus" 0
convertCtxRule (PlusRC _) = Framing "plus" 1
convertCtxRule DefinedC   = Framing "defined" 0

convertPath :: Ctx_path -> [Int]
convertPath Path_nil           = []
convertPath (Path_cons ctx cs) = ctxRule (const (:)) ctx (convertPath cs)

convertRule :: (Monad m)
            => (Simple_proof -> m Int)
            -> Simple_rule -> m (Either Int
                                 (MLRule Text Text Int (AST.Pattern Text Text Int) Int))
convertRule convertHyp r = case r of
  Rule_mp h1 h2 -> Right <$> (ModusPonens <$> convertHyp h2 <*> convertHyp h1)
  -- ^ NB. argument order is flipped!
  Rule_frame ctx hyp -> Right . convertCtxRule ctx <$> convertHyp hyp
  Rule_gen v hyp -> Right . Generalization (nat2Int v) <$> convertHyp hyp
  Rule_use_hyp v -> return (Left (3+nat2Int v))
  Ax_definedness -> return (Left 0)
  Ax_zero_functional -> return (Left 1)
  Ax_succ_functional -> return (Left 2)
  axiom -> pure . Right $ case axiom of
    Ax_propositional1 f1 f2 -> Propositional1 (convertFormula f1) (convertFormula f2)
    Ax_propositional2 f1 f2 f3 -> Propositional2 (convertFormula f1) (convertFormula f2) (convertFormula f3)
    Ax_propositional3 f1 f2 -> Propositional3 (convertFormula f1) (convertFormula f2)
    Ax_varSubst x y p1 _ -> VariableSubstitution (SubstitutedVariable (nat2Int x))
                                                  (convertFormula p1)
                                                  (SubstitutingVariable (nat2Int y))
    Ax_allImp x f1 f2 -> ForallRule (nat2Int x) (convertFormula f1) (convertFormula f2)
    Ax_out_ex ctx var p -> ctxRule PropagateExists ctx (nat2Int var) (convertFormula p)
    Ax_out_or ctx f1 f2 -> ctxRule PropagateOr ctx (convertFormula f1) (convertFormula f2)
    Ax_existence v -> Existence (nat2Int v)
    Ax_singvar path1 path2 v f -> Singvar (nat2Int v) (convertFormula f) (convertPath path1) (convertPath path2)
    Ax_proj1 f1 f2 -> Proj1 (convertFormula f1) (convertFormula f2)
    Ax_proj2 f1 f2 -> Proj2 (convertFormula f1) (convertFormula f2)
    Ax_and_intro f1 f2 -> AndIntro (convertFormula f1) (convertFormula f2)
    Ax_or_elim f1 f2 f3 -> OrElim (convertFormula f1) (convertFormula f2) (convertFormula f3)
    Ax_or_intro1 f1 f2 -> OrIntroL (convertFormula f1) (convertFormula f2)
    Ax_or_intro2 f1 f2 -> OrIntroR (convertFormula f1) (convertFormula f2)
    rule -> error $ "This case should be handled earlier: " ++ show rule
convertFormula :: Formula -> TextPat
convertFormula f = case f of
    Plus f1 f2 -> app "plus" [convertFormula f1, convertFormula f2]
    Succ f1    -> app "succ" [convertFormula f1]
    Zero       -> app "zero" []
    Not f1     -> not (convertFormula f1)
    And f1 f2  -> and (convertFormula f1) (convertFormula f2)
    Var n      -> var (nat2Int n)
    All n f1   -> all (nat2Int n) (convertFormula f1)
    Defined f1 -> app "defined" [convertFormula f1]
  where
    app label args = Fix (AST.Application label args)
    and f1 f2 = Fix (AST.And "Nat" f1 f2)
    all v body = Fix (AST.Forall "Nat" "Nat" v body)
    var v = Fix (AST.Variable "Nat" v)
    not form = Fix (AST.Not "Nat" form)

type TextPat = AST.Pattern Text Text Int
type TextRule = MLRule Text Text Int TextPat
{- The ConvM is for building a proof
   It tracks the next free formula index in the proof,
   and proof lines produced so far, stored in reverse order
 -}
newtype ConvM a = ConvM {runConvM :: State (Int, [(Int,TextPat,TextRule Int)]) a}
  deriving (Functor,Applicative,Monad)

plusSignature :: ValidatedSignature
Just plusSignature = validate $ SignatureInfo
  (Set.fromList ["Nat"])
  (Map.fromList [("defined",("Nat",["Nat"]))
                ,("zero",("Nat",[]))
                ,("succ",("Nat",["Nat"]))
                ,("plus",("Nat",["Nat","Nat"]))
                ])

emit :: TextPat -> TextRule Int -> ConvM Int
emit pat rule = ConvM (state (\(next,lines) -> (next,(next+1,(next,pat,rule):lines))))

convert :: Simple_proof -> ConvM Int
convert (Conclusion formula rule) = convertRule convert rule >>= \case
    Right rule' -> emit (convertFormula formula) rule'
    Left ix -> return ix

useHyp :: (Applicative f) => (Nat -> f Nat) -> (Simple_proof -> f Simple_proof)
useHyp f (Conclusion pat (Rule_use_hyp v)) = Conclusion pat . Rule_use_hyp <$> f v
useHyp _ proof = pure proof

loadCoqOutput :: IO Simple_proof
loadCoqOutput = do
    text <- L.readFile (Paths.dataFileName "test/resources/proof_tree.txt")
    case parse (space1 *> pSimple_proof' <* eof) "proof_tree.txt" text of
        Left err -> error (parseErrorPretty err)
        Right proof -> return proof

{- ^ runConversion takes the number of indices to leave free at the beginning,
   and returns a list of formula lines, with integer indices.
 -}
runConversion :: Int -> Simple_proof -> [(Int,TextPat,TextRule Int)]
runConversion numHyps proof =
    let (_,proofLines) = execState (runConvM (convert proof)) (numHyps,[])
    in reverse proofLines

checkRule :: (ReifiesSignature s)
          => TextRule hypId
          -> Maybe (MLRuleSig (SimpleSignature s) Int hypId)
checkRule = transformRule resolveSort resolveLabel pure checkPattern pure

checkPattern :: (ReifiesSignature s)
             => TextPat -> Maybe (AST.WFPattern (SimpleSignature s) Int)
checkPattern = AST.resolvePattern >=> AST.checkSorts

checkEntry :: (ReifiesSignature s)
           => (Int,TextPat,TextRule Int)
           -> Maybe (Int,AST.WFPattern (SimpleSignature s) Int, MLRuleSig (SimpleSignature s) Int Int)
checkEntry (ix,pat,rule) = (,,) ix <$> checkPattern pat <*> checkRule rule

checkEntry' :: (ReifiesSignature s)
            => proxy (SimpleSignature s)
            -> (Int,TextPat,TextRule Int)
            -> Maybe (Int,AST.WFPattern (SimpleSignature s) Int, MLRuleSig (SimpleSignature s) Int Int)
checkEntry' _proxy = checkEntry


balance :: String -> Tree.Tree String
balance treeString = go (0 :: Int) "<TOP>" [] [] treeString
  where
    go depth parent siblings stack str@('(':str')
      = go (depth+1) str [] ((parent,siblings):stack) str'
    go depth parent siblings ((grandparent,siblings'):stack) (')':str')
      = go (depth-1) grandparent (Tree.Node parent (reverse siblings):siblings') stack str'
    go 0 _ [n] [] "" = n
    go depth parent siblings stack (_:str)
      = go depth parent siblings stack str
    go _ _ _ _ "" = error "balance on the empty string is undefined"

filterTree :: (a -> Bool) -> Tree.Tree a -> Tree.Forest a
filterTree pred (Tree.Node x children) =
    let children' = concatMap (filterTree pred) children
    in if pred x then [Tree.Node x children'] else children'

leaves :: Tree.Tree a -> Tree.Forest a
leaves t@(Tree.Node _ children)
    | null children = [t]
    | otherwise = concatMap leaves children

chomp :: String -> String
chomp str' = go 0 str'
  where
    go :: Int -> String -> String
    go depth ('(':str) = '(':go (depth+1) str
    go 1     (')':_)   = ")"
    go depth (')':str) = ')':go (depth-1) str
    go depth (c  :str) = c:go depth str
    go _     ""        = error "chomp on the empty string is undefined"

findBadThings :: ReifiesSignature s
              => proxy (SimpleSignature s)
              -> [(Int,TextPat,TextRule Int)]
              -> [(Int,TextPat,TextRule Int)]
findBadThings proxy entries =
    [e | e <- entries, checkEntry' proxy e == Nothing]

loadConverted :: IO [(Int,TextPat,TextRule Int)]
loadConverted = do
    p <- loadCoqOutput
    return (runConversion 5 p)
      {- Hypothesis ids 0,1,2 are used for definedness, zero functional, and one-functional
         in the translation above, and the 1+1 proof has two further hypotheses
         about plus(zero,x) and plus(succ(x),y),
         so 5 is the next free id -}

startProof :: (ReifiesSignature s)
           => proxy (SimpleSignature s)
           -> Either String (Proof Int
                       (MLRuleSig (SimpleSignature s) Int)
                       (AST.WFPattern (SimpleSignature s) Int))
startProof _proxy = do
    assumptions <- maybe (Left "Bad pattern") Right $ mapM checkPattern
        [defined (var 0)
        -- ^ definedness
        ,ex 1 (eqlP (var 1) zero)
        -- ^ zero functional
        ,ex 1 (eqlP (var 1) (succ (var 0)))
        -- ^ succ functional
        ,AST.impliesP "Nat" (plus zero (var 0)) (var 0)
        -- ^ definition of plus zero
        ,AST.impliesP "Nat" (plus (succ (var 0)) (var 1)) (succ (plus (var 0) (var 1)))
        -- ^ definition of plus succ
        ]
    foldM (\pf (ix,pat) -> either (Left . show) Right
               $ add (\_->Right ()) pf ix pat)
      emptyProof (zip [0..] assumptions)
  where
    defined p = AST.applicationP "defined" [p]
    zero = AST.applicationP "zero" []
    succ p = AST.applicationP "succ" [p]
    plus a b = AST.applicationP "plus" [a,b]
    total p = AST.notP "Nat" (defined (AST.notP "Nat" p))
    ex n = AST.existsP "Nat" "Nat" n
    var n = AST.variableP "Nat" n
    eqlP l r = total (AST.iffP "Nat" l r)

runEntry :: (ReifiesSignature s)
         => Proof Int
              (MLRuleSig (SimpleSignature s) Int)
              (AST.WFPattern (SimpleSignature s) Int)
         -> (Int,AST.WFPattern (SimpleSignature s) Int,
              MLRuleSig (SimpleSignature s) Int Int)
         -> Either String (Proof Int
              (MLRuleSig (SimpleSignature s) Int)
              (AST.WFPattern (SimpleSignature s) Int))
runEntry proof entry@(ix,pat,rule) = presentError $ do
    proof1 <- add (const (Right ())) proof ix pat
    derive proof1 ix rule
  where
    presentError (Left err) =
        Left ("Error processing "++show entry++":\n"++show err)
    presentError (Right val) = Right val

withProof :: (forall (s :: *). (ReifiesSignature s) =>
              Either String (Proof Int
                      (MLRuleSig (SimpleSignature s) Int)
                      (AST.WFPattern (SimpleSignature s) Int))
              -> IO r)
          -> IO r
withProof body = do
    entries <- loadConverted
    reifySignature plusSignature (\proxy -> body $ do
        axioms <- startProof proxy
        foldM (\pf -> (maybe (Left "Check failed") Right . checkEntry)
                      >=> runEntry pf) axioms entries)

example :: IO [(Int,TextPat,TextRule Int)]
example = do
    entries <- loadConverted
    return $ reifySignature plusSignature (flip findBadThings entries)

test_minimalOnePlusOne :: TestTree
test_minimalOnePlusOne =
    testCase "Minimal 1+1=2 Proof" $ withProof $ \case
        Left message -> assertFailure message
        Right _ -> return ()

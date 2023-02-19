module Language.CP where

import Prelude

import Control.Monad.State (gets)
import Data.Array ((!!))
import Data.Either (Either(..))
import Data.List (foldl)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import Language.CP.CodeGen (runCodeGen)
import Language.CP.Context (Checking, CompilerState, Mode(..), Pos(..), TypeError(..), Typing, initState, runChecking, throwCheckError, throwTypeError)
import Language.CP.Desugar (desugar, desugarProg)
import Language.CP.Parser (expr, program, whiteSpace)
import Language.CP.Semantics.HOAS as HOAS
import Language.CP.Semantics.NaturalClosure as Closure
import Language.CP.Semantics.NaturalSubst as BigStep
import Language.CP.Semantics.StepTrace as StepTrace
import Language.CP.Semantics.Subst as SmallStep
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.Typing (checkProg, infer)
import Language.JS.Pretty (print)
import Parsing (ParseError(..), Position(..), runParser)
import Parsing.String (eof)

inferType :: String -> Typing String
inferType code = case runParser code (whiteSpace *> expr <* eof) of
  Left err -> throwTypeError $ showParseError err code
  Right e -> do
    _ /\ t <- infer $ desugar e
    pure $ show t

importDefs :: String -> Checking Unit
importDefs code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> do
    let prog' = desugarProg prog
    _ <- checkProg prog'
    pure unit

elaborateProg :: S.Prog -> Checking C.Tm
elaborateProg p = gets =<< wrapUp <<< fst <$> checkProg p
  where
    wrapUp :: C.Tm -> CompilerState -> C.Tm
    wrapUp e st = foldl (#) e $ snd <$> st.tmBindings

evalProg :: S.Prog -> Checking String
evalProg prog = do
  let prog'@(S.Prog _ e') = desugarProg prog
  e <- elaborateProg prog'
  mode <- gets (_.mode)
  pure $ case mode of
    SmallStep -> show (SmallStep.eval e)
    StepTrace -> let _ /\ s = StepTrace.eval e in
      show prog <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> s ""
    BigStep -> show (BigStep.eval e)
    HOAS -> show (HOAS.eval e)
    Closure -> show (Closure.eval e)

-- Source code interpretation used by REPL
interpret :: String -> Checking String
interpret code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> evalProg prog

-- Big-step evaluation used after ANTLR parsing
evaluate :: S.Prog -> Effect String
evaluate prog = case runChecking (evalProg prog) initState of
  Left err -> throw $ showTypeError err
  Right (output /\ _) -> pure output

compile :: String -> Either String String
compile code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> Left $ showParseError err code
  Right prog -> case runChecking (elaborateProg (desugarProg prog)) initState of
    Left err -> Left $ showTypeError err
    Right (e /\ _) -> print <$> runCodeGen e

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError _ pos@(Position { line: l, column: c })) source =
  showPosition pos <> ": parse error:\n" <>
  case seek l of Just line -> line <> "\n" <> rep (c-1) " " <> "^"
                 Nothing -> ""
  where
    seek :: Int -> Maybe String
    seek line = (split (Pattern "\n") source) !! (line - 1)
    rep :: Int -> String -> String
    rep n s | n <= 0 = ""
            | otherwise = s <> rep (n-1) s

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr inDoc)) =
  showPosition pos <> ": " <> msg <> "\nin the expression: " <>
  (if inDoc then S.showDoc else show) expr

module Text.IndentingPrinter
    ( PrinterOutput (write, betweenLines, withIndent)
    , printToString
    , StringPrinter
    , docToString
    ) where

import Control.Monad.Writer
import Data.String
       ( IsString (..) )

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String

class Monad m => PrinterOutput m where
    write :: String -> m ()
    betweenLines :: m ()
    withIndent :: Int -> m () -> m ()

type StringPrinter = Writer (Doc ())

instance PrinterOutput (Writer (Doc ())) where
    write s = tell (fromString s)
    betweenLines = tell line
    withIndent n m = censor (nest n) m

printToString :: StringPrinter () -> String
printToString printer = renderString simpleStream
    where
      doc = execWriter printer
      simpleStream = layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded}) doc

{- | Renders a 'Doc' as a 'String', with 'Unbounded' page width
     (no automatic wrapping). -}
docToString :: Doc ann -> String
docToString doc = renderString simpleStream
  where
    simpleStream = layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded}) doc

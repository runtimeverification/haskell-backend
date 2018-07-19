{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Data.Kore.IndentingPrinter ( betweenLines
                                  , PrinterOutput
                                  , printToString
                                  , StringPrinter
                                  , withIndent
                                  , write
                                  ) where

import Control.Monad.Reader
import Control.Monad.Writer

class FromString a where
    fromString :: String -> a

instance FromString ShowS where
    fromString = showString

class (FromString w, MonadWriter w m, MonadReader Int m)
    => PrinterOutput w m where
    write :: String -> m ()
    write s = tell (fromString s)

    betweenLines :: m ()
    betweenLines = do
        indent <- reader (`replicate` ' ')
        write "\n"
        write indent

    withIndent :: Int -> m () -> m ()
    withIndent n = local (+n)

type StringPrinter = WriterT ShowS (Reader Int)

instance PrinterOutput ShowS StringPrinter where

printToString :: StringPrinter () -> String
printToString printer = showChain ""
    where
    writerAction = printer
    readerAction = execWriterT writerAction
    showChain = runReader readerAction 0

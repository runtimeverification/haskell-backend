module Main (main) where

import qualified Options.Applicative as Options
import qualified Speedscope.Main as Speedscope
import Prelude

main :: IO ()
main =
    Speedscope.main =<< Options.execParser info
  where
    info =
        Options.info
            (Speedscope.parseOptions Options.<**> Options.helper)
            ( mconcat
                [ Options.fullDesc
                , Options.progDesc "Write a speedscope profile for FILENAME"
                , Options.header "kore-prof - Kore profiler"
                ]
            )

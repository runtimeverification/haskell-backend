{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Stats
    ( Stats (..)
    , getStats
    , writeStats
    , readStats
    ) where

import Prelude.Kore

import Data.Aeson
    ( FromJSON
    , ToJSON
    )
import qualified Data.Aeson as Aeson
import Data.Word
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import qualified GHC.Stats as GHC
import qualified System.Mem as System

import Debug

data Stats =
    Stats
        { gcs, major_gcs :: !Word32
        , allocated_bytes, max_live_bytes :: !Word64
        , mutator_cpu_ns, mutator_elapsed_ns :: !GHC.RtsTime
        , gc_cpu_ns, gc_elapsed_ns :: !GHC.RtsTime
        , cpu_ns, elapsed_ns :: !GHC.RtsTime
        }
    deriving (Eq, Read, Show)
    deriving (GHC.Generic)

instance FromJSON Stats

instance ToJSON Stats

instance SOP.Generic Stats

instance SOP.HasDatatypeInfo Stats

instance Debug Stats

instance Diff Stats

fromGHC :: GHC.RTSStats -> Stats
fromGHC rtsStats =
    Stats
        { gcs, major_gcs
        , allocated_bytes, max_live_bytes
        , mutator_cpu_ns, mutator_elapsed_ns
        , gc_cpu_ns, gc_elapsed_ns
        , cpu_ns, elapsed_ns
        }
  where
    GHC.RTSStats
        { gcs, major_gcs
        , allocated_bytes, max_live_bytes
        , mutator_cpu_ns, mutator_elapsed_ns
        , gc_cpu_ns, gc_elapsed_ns
        , cpu_ns, elapsed_ns
        }
      = rtsStats

getStats :: IO Stats
getStats = do
    -- Some counters are only updated after a major GC.
    System.performMajorGC
    fromGHC <$> GHC.getRTSStats

writeStats :: FilePath -> Stats -> IO ()
writeStats = Aeson.encodeFile

readStats :: FilePath -> IO Stats
readStats filePath =
    either errorWith return =<< Aeson.eitherDecodeFileStrict filePath
  where
    errorWith message = error ("readStats: " ++ message)

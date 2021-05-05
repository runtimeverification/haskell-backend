{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}

module Kore.Attribute.Definition (
    parseKFileAttributes,
    KFileLocations (..)
 ) where

import Prelude.Kore
import Kore.Attribute.Attributes ( Attributes(..) )
import Kore.Attribute.SourceLocation ( SourceLocation )
import qualified Data.Default as Default
import Kore.Attribute.Parser ( ParseAttributes(..) )
import Data.Generics.Product ( typed )
import Kore.Log.ErrorParse
import Kore.Error ( printError )
import Control.Monad.Catch (MonadThrow)

newtype KFileLocations =
    KFileLocations
        { locations :: [SourceLocation] }
    deriving stock Show

parseKFileAttributes :: MonadThrow m => Attributes -> m SourceLocation
parseKFileAttributes (Attributes attrs) =
    case parser of
        Left err -> errorParse $ printError err
        Right sourceLocation ->
            return sourceLocation
  where
    parser = foldlM (flip parseDefinitionLocation) Default.def attrs
    parseDefinitionLocation source =
        typed @SourceLocation (parseAttribute source)

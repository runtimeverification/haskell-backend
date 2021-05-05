module Kore.Attribute.Definition (
    parseKFileAttributes,
    KFileLocations (..),
) where

import Control.Monad.Catch (MonadThrow)
import qualified Data.Default as Default
import Data.Generics.Product (typed)
import Kore.Attribute.Attributes (Attributes (..))
import Kore.Attribute.Parser (ParseAttributes (..))
import Kore.Attribute.SourceLocation (SourceLocation)
import Kore.Error (printError)
import Kore.Log.ErrorParse
import Prelude.Kore

newtype KFileLocations = KFileLocations
    {locations :: [SourceLocation]}
    deriving stock (Show)

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

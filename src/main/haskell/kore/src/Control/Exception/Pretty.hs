module Control.Exception.Pretty
    ( PrettyException (..)
    , displayPrettyException
    ) where

import           Control.Exception
                 ( Exception, SomeException )
import qualified Control.Exception as Exception
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text as Render
import           Data.Typeable
                 ( Typeable )
import           System.IO
                 ( stderr )

{- | A type of 'Exception' which can be displayed nicely for the user.

By the time a @PrettyException@ has been constructed, the exception has already
been converted to a 'Doc'.

Use 'displayPrettyException' to decode a possible 'PrettyException' and display
it nicely.

 -}
data PrettyException =
    forall e. (Pretty e, Exception e) =>
    PrettyException e
    deriving (Typeable)

instance Pretty PrettyException where
    pretty (PrettyException e) = pretty e

instance Show PrettyException where
    show = show . pretty

instance Exception PrettyException

{- | Decode and display a 'PrettyException'.

If the provided 'SomeException' is not a 'PrettyException', it will be rethrown.

 -}
displayPrettyException :: SomeException -> IO ()
displayPrettyException exn =
    case Exception.fromException exn of
        Just (PrettyException e) ->
            Render.hPutDoc stderr
                -- Ensure that the message has a trailing newline.
                (pretty e <> hardline)
        Nothing ->
            Exception.throwIO exn

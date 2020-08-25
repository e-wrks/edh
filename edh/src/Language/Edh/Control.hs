
module Language.Edh.Control where

import           Prelude

import           Control.Exception
import           Control.Monad.State.Strict

import           Data.Void
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Text.Megaparsec         hiding ( State )


type OpSymbol = Text
type Precedence = Int

-- use such a dict as the parsing state, to implement
-- object-language-declarable operator precendence
type OpPrecDict = Map.HashMap OpSymbol (Precedence, Text)

-- no backtracking needed for precedence dict, so it
-- can live in the inner monad of 'ParsecT'.
type Parser = ParsecT Void Text (State OpPrecDict)

-- so goes this simplified parsing err type name
type ParserError = ParseErrorBundle Text Void


data EdhCallFrame = EdhCallFrame {
    edh'callee'proc'name :: !Text
  , edh'callee'defi'loca :: !Text
  , edh'caller'from'loca :: !Text
  } deriving (Eq)
instance Show EdhCallFrame where
  show = T.unpack . dispEdhCallFrame
dispEdhCallFrame :: EdhCallFrame -> Text
dispEdhCallFrame (EdhCallFrame !pname !pdefi !pcaller) =
  "📜 " <> pname <> " 🔎 " <> pdefi <> " 👈 " <> pcaller

data EdhCallContext = EdhCallContext {
    edh'call'tip'loca :: !Text
  , edh'call'frames   :: ![EdhCallFrame]
  } deriving (Eq)
instance Show EdhCallContext where
  show = T.unpack . dispEdhCallContext
dispEdhCallContext :: EdhCallContext -> Text
dispEdhCallContext (EdhCallContext !tip !frames) =
  T.unlines $ (dispEdhCallFrame <$> frames) ++ ["👉 " <> tip]


data EdhError =
    -- | thrown to halt the whole Edh program with a result, this is not
    -- catchable by Edh code
    ProgramHalt !Dynamic

    -- | arbitrary realworld error happened in IO, propagated into the Edh
    -- world
  | EdhIOError !SomeException

    -- | error occurred remotely, detailed text captured for display on the
    -- throwing site
  | EdhPeerError !Text !Text

    -- | tagged error, with a msg and context information of the throwing Edh
    -- thread
  | EdhError !EdhErrorTag !Text !Dynamic !EdhCallContext

instance Exception EdhError

instance Show EdhError where
  show (ProgramHalt _  ) = "Edh⏹️Halt"
  show (EdhIOError  ioe) = show ioe
  show (EdhPeerError peerSite details) = --
    "🏗️ " <> T.unpack peerSite <> "\n" <> T.unpack details
  show (EdhError EdhException !msg _details !cc) = --
    "Đ\n" <> show cc <> T.unpack msg
  show (EdhError PackageError !msg _details !cc) = --
    "💔\n" <> show cc <> "📦 " <> T.unpack msg
  show (EdhError ParseError !msg _details !cc) = --
    "💔\n" <> show cc <> "⛔ " <> T.unpack msg
  show (EdhError EvalError !msg _details !cc) = --
    "💔\n" <> show cc <> "💣 " <> T.unpack msg
  show (EdhError UsageError !msg _details !cc) = --
    "💔\n" <> show cc <> "🙈 " <> T.unpack msg

data EdhErrorTag =
    EdhException -- for root class of custom Edh exceptions
  | PackageError
  | ParseError
  | EvalError
  | UsageError
  deriving (Eq, Show)


edhKnownError :: SomeException -> Maybe EdhError
edhKnownError exc = case fromException exc of
  Just (err :: EdhError) -> Just err
  Nothing                -> case fromException exc of
    Just (err :: ParserError) ->
      Just
        $ EdhError ParseError (T.pack $ errorBundlePretty err) (toDyn ())
        $ EdhCallContext "<parsing>" []
    Nothing -> Nothing


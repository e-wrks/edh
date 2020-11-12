
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
data OpFixity = InfixL | InfixR | Infix
  deriving Eq
instance Show OpFixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix  = "infix"
type Precedence = Int
type OpDeclLoc = Text

-- global dict for operator info, as the parsing state
type GlobalOpDict = Map.HashMap OpSymbol (OpFixity, Precedence, OpDeclLoc)

-- no backtracking needed for precedence dict, so it
-- can live in the inner monad of 'ParsecT'.
type Parser = ParsecT Void Text (State GlobalOpDict)

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
  -- | thrown to halt the whole Edh program with a result
  --
  -- this is not recoverable by Edh code
  --
  -- caveat: never make this available to a sandboxed environment
    ProgramHalt !Dynamic

  -- | thrown when an Edh thread is terminated, usually incurred by {break}
  -- from an event perceiver, but can also be thrown explicitly from normal
  -- Edh code
  --
  -- this is not recoverable by Edh code
  --
  -- caveat: never make this available to a sandboxed environment
  | ThreadTerminate

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
  show (ProgramHalt _)  = "Edh⏹️Halt"
  show ThreadTerminate  = "Edh🛑Terminate"
  show (EdhIOError ioe) = show ioe
  show (EdhPeerError peerSite details) = --
    "🏗️ traceback: " <> T.unpack peerSite <> "\n" <> T.unpack details
  show (EdhError EdhException !msg _details !cc) = --
    "Đ traceback\n" <> show cc <> T.unpack msg
  show (EdhError PackageError !msg _details !cc) = --
    "💔 traceback\n" <> show cc <> "📦 " <> T.unpack msg
  show (EdhError ParseError !msg _details !cc) = --
    "💔 traceback\n" <> show cc <> "⛔ " <> T.unpack msg
  show (EdhError EvalError !msg _details !cc) = --
    "💔 traceback\n" <> show cc <> "💣 " <> T.unpack msg
  show (EdhError UsageError !msg _details !cc) = --
    "💔 traceback\n" <> show cc <> "🙈 " <> T.unpack msg

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


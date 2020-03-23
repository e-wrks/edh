
module Language.Edh.Control where

import           Prelude

import           Control.Exception
import           Control.Monad.State.Strict

import           Data.Void
import           Data.Typeable
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

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
      edhCalleeProcName :: !Text
    , edhCalleeDefiLoca :: !Text
    , edhCallerFromLoca :: !Text
  } deriving (Eq, Typeable)
instance Show EdhCallFrame where
  show = T.unpack . dispEdhCallFrame
dispEdhCallFrame :: EdhCallFrame -> Text
dispEdhCallFrame (EdhCallFrame !pname !pdefi !pcaller) =
  "📜 " <> pname <> " 🔎 " <> pdefi <> " 👈 " <> pcaller

data EdhCallContext = EdhCallContext {
      edhCallTipLoca :: !Text
    , edhCallFrames :: ![EdhCallFrame]
  } deriving (Eq, Typeable)
instance Show EdhCallContext where
  show = T.unpack . dispEdhCallContext
dispEdhCallContext :: EdhCallContext -> Text
dispEdhCallContext (EdhCallContext !tip !frames) =
  T.unlines $ (dispEdhCallFrame <$> frames) ++ ["👉 " <> tip]


data EdhError =
      PackageError !Text
    | ParseError !ParserError !EdhCallContext
    | EvalError !Text !EdhCallContext
    | UsageError !Text !EdhCallContext
  deriving (Eq, Typeable)
instance Show EdhError where
  show (PackageError !msg) = "📦 " <> T.unpack msg
  show (ParseError !err !ctx) =
    "💔\n" <> show ctx <> "⛔ " <> errorBundlePretty err
  show (EvalError  !msg !ctx) = "💔\n" <> show ctx <> "💣 " <> T.unpack msg
  show (UsageError !msg !ctx) = "💔\n" <> show ctx <> "🙈 " <> T.unpack msg
instance Exception EdhError


edhKnownError :: SomeException -> Maybe EdhError
edhKnownError err = case fromException err :: Maybe EdhError of
  Just e  -> Just e
  Nothing -> case fromException err :: Maybe ParserError of
    Just e  -> Just $ ParseError e $ EdhCallContext "<parsing>" []
    Nothing -> Nothing


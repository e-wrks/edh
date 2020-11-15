
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


-- | Source document
--
-- absolute local (though possibly network mounted) file path if started with
-- '/', otherwise should be valid URI
newtype SrcDoc = SrcDoc Text
  deriving (Eq, Show)

-- | Source position
-- in LSP convention, i.e. no document locator
data SrcPos = SrcPos {
    -- in LSP convention, i.e. zero based
    src'line :: !Int
    -- in LSP convention, i.e. zero based
  , src'char :: !Int
  } deriving (Eq, Show)

-- | Source range
-- in LSP convention, i.e. no document locator
data SrcRange = SrcRange {
    -- in LSP convention, i.e. zero based
    src'start :: {-# UNPACK #-} !SrcPos
    -- in LSP convention, i.e. zero based
  , src'end :: {-# UNPACK #-} !SrcPos
  } deriving (Eq, Show)

-- | Source location
data SrcLoc = SrcLoc {
    src'doc :: {-# UNPACK #-} !SrcDoc
  , src'range :: {-# UNPACK #-} !SrcRange
  } deriving (Eq, Show)


lspSrcPosFromParsec :: SourcePos -> SrcPos
lspSrcPosFromParsec !sp =
  SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1)

lspSrcLocFromParsec :: SourcePos -> SrcPos -> SrcLoc
lspSrcLocFromParsec !sp !end =
  SrcLoc (SrcDoc $ T.pack $ sourceName sp) $ SrcRange
    (SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1))
    end


startLocOfFile :: FilePath -> SrcLoc
startLocOfFile !n =
  SrcLoc (SrcDoc $ T.pack n) (SrcRange (SrcPos 0 0) (SrcPos 0 0))
prettySrcSpan :: SrcLoc -> Text
prettySrcSpan (SrcLoc (SrcDoc !doc) (SrcRange (SrcPos !start'line !start'char) (SrcPos !end'line !end'char)))
  | end'line == start'line && end'char == start'char
  = if start'line == 0 && start'char == 0
    then doc
    else doc <> ":" <> T.pack (show $ 1 + start'line) <> ":" <> T.pack
      (show $ 1 + start'char)
  | otherwise
  = doc
    <> ":"
    <> T.pack (show $ 1 + start'line)
    <> ":"
    <> T.pack (show $ 1 + start'char)
    <> "-"
    <> T.pack (show $ 1 + end'line)
    <> ":"
    <> T.pack (show $ 1 + end'char)


data EdhParserState = EdhParserState {
    -- global dict for operator info, as the parsing state
    edh'parser'op'dict :: !GlobalOpDict
    -- end of last lexeme
  , edh'parser'lexeme'end :: !SrcPos
  }
type GlobalOpDict = Map.HashMap OpSymbol (OpFixity, Precedence, OpDeclLoc)

-- no backtracking needed for precedence dict, so it
-- can live in the inner monad of 'ParsecT'.
type Parser = ParsecT Void Text (State EdhParserState)

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


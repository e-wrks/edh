module Language.Edh.Control where

import Control.Exception
  ( Exception (fromException),
    SomeException,
  )
import Control.Monad.State.Strict (State)
import Data.Dynamic (Dynamic, toDyn)
import qualified Data.HashMap.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
  ( ParseErrorBundle,
    ParsecT,
    SourcePos (sourceColumn, sourceLine, sourceName),
    errorBundlePretty,
    unPos,
  )
import Prelude

type OpSymSrc = (OpSymbol, SrcRange)

type OpSymbol = Text

data OpFixity = InfixL | InfixR | Infix
  deriving (Eq)

instance Show OpFixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix = "infix"

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
data SrcPos = SrcPos
  { -- in LSP convention, i.e. zero based
    src'line :: !Int,
    -- in LSP convention, i.e. zero based
    src'char :: !Int
  }
  deriving (Eq, Show)

instance Ord SrcPos where
  compare (SrcPos !x'l !x'c) (SrcPos !y'l !y'c) = case compare x'l y'l of
    EQ -> compare x'c y'c
    !conclusion -> conclusion

beginningSrcPos :: SrcPos
beginningSrcPos = SrcPos 0 0

-- | Source range
-- in LSP convention, i.e. no document locator
data SrcRange = SrcRange
  { -- in LSP convention, i.e. zero based
    src'start :: {-# UNPACK #-} !SrcPos,
    -- in LSP convention, i.e. zero based
    src'end :: {-# UNPACK #-} !SrcPos
  }
  deriving (Eq, Show)

-- | compare a position to a range, return 'EQ' when the position is within the
-- range, or 'LT' when before it, 'GT' when after it.
srcPosCmp2Range :: SrcPos -> SrcRange -> Ordering
srcPosCmp2Range !p (SrcRange !start !end) = case compare p start of
  LT -> LT
  EQ -> EQ
  GT ->
    if src'line end < 0
      then EQ -- special infinite end
      else case compare p end of
        LT -> EQ
        EQ -> EQ -- end position of a range is inclusive per VSCode word pick
        GT -> GT

zeroSrcRange :: SrcRange
zeroSrcRange = SrcRange beginningSrcPos beginningSrcPos

noSrcRange :: SrcRange
noSrcRange = SrcRange (SrcPos (-1) (-1)) (SrcPos (-1) (-1))

prettySrcPos :: SrcDoc -> SrcPos -> Text
prettySrcPos (SrcDoc !file) (SrcPos !line !char)
  | line < 0 || char < 0 = "<host-code>"
  | otherwise =
    file <> ":" <> T.pack (show $ 1 + line) <> ":"
      <> T.pack
        (show $ 1 + char)

prettySrcRange :: SrcDoc -> SrcRange -> Text
prettySrcRange (SrcDoc !file) (SrcRange (SrcPos !start'line !start'char) (SrcPos !end'line !end'char))
  | start'line < 0 || start'char < 0 =
    "<host-code>"
  | end'line == 0 && end'char == 0 =
    file
  | end'line == start'line && end'char == start'char =
    file <> ":" <> T.pack (show $ 1 + start'line) <> ":"
      <> T.pack
        (show $ 1 + start'char)
  | otherwise =
    file
      <> ":"
      <> T.pack (show $ 1 + start'line)
      <> ":"
      <> T.pack (show $ 1 + start'char)
      <> "-"
      <> T.pack (show $ 1 + end'line)
      <> ":"
      <> T.pack (show $ 1 + end'char)

-- | Source location
data SrcLoc = SrcLoc
  { src'doc :: {-# UNPACK #-} !SrcDoc,
    src'range :: {-# UNPACK #-} !SrcRange
  }
  deriving (Eq, Show)

prettySrcLoc :: SrcLoc -> Text
prettySrcLoc (SrcLoc !doc !range) = prettySrcRange doc range

lspSrcPosFromParsec :: SourcePos -> SrcPos
lspSrcPosFromParsec !sp =
  SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1)

lspSrcLocFromParsec :: SourcePos -> SrcPos -> SrcLoc
lspSrcLocFromParsec !sp !end =
  SrcLoc (SrcDoc $ T.pack $ sourceName sp) $
    SrcRange
      (SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1))
      end

lspSrcRangeFromParsec :: SourcePos -> SrcPos -> SrcRange
lspSrcRangeFromParsec !sp !end =
  SrcRange
    (SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1))
    end

lspSrcRangeFromParsec' :: SrcPos -> SourcePos -> SrcRange
lspSrcRangeFromParsec' !start !sp =
  SrcRange
    start
    (SrcPos (unPos (sourceLine sp) - 1) (unPos (sourceColumn sp) - 1))

data EdhParserState = EdhParserState
  { -- global dict for operator info, as the parsing state
    edh'parser'op'dict :: !GlobalOpDict,
    -- end of last lexeme
    edh'parser'lexeme'end :: !SrcPos
  }

type GlobalOpDict = Map.HashMap OpSymbol (OpFixity, Precedence, OpDeclLoc)

-- no backtracking needed for precedence dict, so it
-- can live in the inner monad of 'ParsecT'.
type Parser = ParsecT Void Text (State EdhParserState)

-- so goes this simplified parsing err type name
type ParserError = ParseErrorBundle Text Void

-- TODO declare `HasCallStack =>` for each ctor?
data EdhError
  = -- | thrown to halt the whole Edh program with a result
    --
    -- this is not recoverable by Edh code
    --
    -- caveat: never make this available to a sandboxed environment
    ProgramHalt !Dynamic
  | -- | thrown when an Edh thread is terminated, usually incurred by {break}
    -- from an event perceiver, but can also be thrown explicitly from normal
    -- Edh code
    --
    -- this is not recoverable by Edh code
    --
    -- caveat: never make this available to a sandboxed environment
    ThreadTerminate
  | -- | arbitrary realworld error happened in IO, propagated into the Edh
    -- world
    EdhIOError !SomeException
  | -- | error occurred remotely, detailed text captured for display on the
    -- throwing site
    EdhPeerError !PeerSite !ErrDetails
  | -- | tagged error, with a msg and context information of the throwing Edh
    -- thread
    EdhError !EdhErrorTag !ErrMessage !Dynamic !ErrContext

type PeerSite = Text

type ErrDetails = Text

type ErrMessage = Text

type ErrContext = Text

instance Exception EdhError

instance Show EdhError where
  show (ProgramHalt _) = "Edh⏹️Halt"
  show ThreadTerminate = "Edh❎Terminate"
  show (EdhIOError !ioe) = show ioe
  show (EdhPeerError !peerSite !details) =
    T.unpack $ "🏗️ traceback: " <> peerSite <> "\n" <> details
  show (EdhError EdhException !msg _details !ctx) =
    T.unpack $ "Đ traceback\n" <> ctx <> msg
  show (EdhError PackageError !msg _details !ctx) =
    T.unpack $ "💔 traceback\n" <> ctx <> "📦 " <> msg
  show (EdhError ParseError !msg _details !ctx) =
    T.unpack $ "💔 traceback\n" <> ctx <> "⛔ " <> msg
  show (EdhError EvalError !msg _details !ctx) =
    T.unpack $ "💔 traceback\n" <> ctx <> "💣 " <> msg
  show (EdhError UsageError !msg _details !ctx) =
    T.unpack $ "💔 traceback\n" <> ctx <> "🙈 " <> msg

data EdhErrorTag
  = EdhException -- for root class of custom Edh exceptions
  | PackageError
  | ParseError
  | EvalError
  | UsageError
  deriving (Eq, Show)

edhKnownError :: SomeException -> Maybe EdhError
edhKnownError exc = case fromException exc of
  Just (err :: EdhError) -> Just err
  Nothing -> case fromException exc of
    Just (err :: ParserError) ->
      Just $
        EdhError
          ParseError
          (T.pack $ errorBundlePretty err)
          (toDyn ())
          "<parsing>"
    Nothing -> Nothing

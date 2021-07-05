module Language.Edh.Control where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad.State.Strict (State)
import qualified Data.Char as Char
import Data.Dynamic (Dynamic, toDyn)
import qualified Data.HashMap.Strict as Map
import qualified Data.List as L
import Data.Maybe
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

data OpSymSrc = OpSymSrc !OpSymbol !SrcRange
  deriving (Eq)

instance Show OpSymSrc where
  show (OpSymSrc sym _) = show sym

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

lspSrcRangeFromParsec'' :: SourcePos -> SourcePos -> SrcRange
lspSrcRangeFromParsec'' !start !end =
  SrcRange
    (SrcPos (unPos (sourceLine start) - 1) (unPos (sourceColumn start) - 1))
    (SrcPos (unPos (sourceLine end) - 1) (unPos (sourceColumn end) - 1))

data EdhParserState = EdhParserState
  { -- global dict for operator info, as the parsing state
    edh'parser'op'dict :: !GlobalOpDict,
    -- end of last lexeme
    edh'parser'lexeme'end'pos :: !SrcPos,
    edh'parser'lexeme'end'offset :: !Int
  }

data GlobalOpDict = GlobalOpDict
  { -- | precedence & fixity of known operators
    operator'declarations ::
      Map.HashMap OpSymbol (OpFixity, Precedence, OpDeclLoc),
    -- | operators with non-standard character(s) in their symbol
    -- invariant: ascendingly sorted,
    -- so parsing against this list should attempt in reverse order
    quaint'operators :: [OpSymbol]
  }

lookupOpFromDict ::
  OpSymbol -> GlobalOpDict -> Maybe (OpFixity, Precedence, OpDeclLoc)
lookupOpFromDict !sym (GlobalOpDict !decls _) = Map.lookup sym decls

insertOpIntoDict ::
  OpSymbol -> (OpFixity, Precedence, OpDeclLoc) -> GlobalOpDict -> GlobalOpDict
insertOpIntoDict !sym !decl (GlobalOpDict !decls !quaint'ops) =
  GlobalOpDict (Map.insert sym decl decls) $
    if contain'nonstd'op'char
      then L.insert sym quaint'ops
      else quaint'ops
  where
    contain'nonstd'op'char :: Bool
    contain'nonstd'op'char = isJust $ T.find (not . isOperatorChar) sym

mergeOpDict :: TVar GlobalOpDict -> GlobalOpDict -> GlobalOpDict -> IO ()
mergeOpDict
  godv
  (GlobalOpDict !base'decls !base'quaint'ops)
  (GlobalOpDict !decls !quaint'ops) =
    if Map.null declUpds && L.null quaintUpds
      then return () -- shortcircuit without touching the TVar
      else atomically $
        modifyTVar' godv $ \(GlobalOpDict !curr'decls !curr'quaint'ops) ->
          GlobalOpDict
            ( if Map.null declUpds
                then curr'decls
                else Map.union curr'decls declUpds
            )
            ( if L.null quaintUpds
                then curr'quaint'ops
                else L.sort $ curr'quaint'ops ++ quaintUpds
            )
    where
      declUpds = Map.difference decls base'decls
      quaintUpds =
        if L.length quaint'ops <= L.length base'quaint'ops
          then [] -- shortcircuit since we know both are sorted and no removal
          else quaint'ops L.\\ base'quaint'ops

isOperatorChar :: Char -> Bool
isOperatorChar !c =
  if c < toEnum 128
    then c `elem` ("=!@#$%^&|:<>?*+-/" :: [Char])
    else case Char.generalCategory c of
      Char.MathSymbol -> True
      Char.CurrencySymbol -> True
      Char.ModifierSymbol -> True
      Char.OtherSymbol -> True
      Char.DashPunctuation -> True
      Char.OtherPunctuation -> True
      _ -> False

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
  show (EdhError UserCancel !msg _details !ctx) =
    T.unpack $ "💔 traceback\n" <> ctx <> "🛑 " <> msg

data EdhErrorTag
  = EdhException -- for root class of custom Edh exceptions
  | PackageError
  | ParseError
  | EvalError
  | UsageError
  | UserCancel
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

module Language.Edh.Batteries
  ( defaultEdhConsoleSettings,
    defaultEdhConsole,
    installEdhBatteries,
    module Language.Edh.Batteries.Data,
    module Language.Edh.Batteries.Math,
    module Language.Edh.Batteries.Assign,
    module Language.Edh.Batteries.Reflect,
    module Language.Edh.Batteries.Ctrl,
    module Language.Edh.Batteries.Console,
    module Language.Edh.Batteries.Evt,
    module Language.Edh.Batteries.Vector,
  )
where

import Control.Concurrent (forkIOWithUnmask)
import Control.Concurrent.STM
import Control.Exception (bracket, finally, mask_)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Void (Void)
import Language.Edh.Batteries.Assign
  ( assignMissingProc,
    assignProc,
    assignWithOpProc,
  )
import Language.Edh.Batteries.Console
import Language.Edh.Batteries.Ctrl
import Language.Edh.Batteries.Data
import Language.Edh.Batteries.Evt
import Language.Edh.Batteries.Math
import Language.Edh.Batteries.Reflect
import Language.Edh.Batteries.Vector
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.InterOp
import Language.Edh.RtTypes
import Language.Edh.Runtime
import System.Console.Haskeline
  ( InputT,
    Settings (..),
    getInputLine,
    getPassword,
    handleInterrupt,
    outputStr,
    outputStrLn,
    runInputT,
    withInterrupt,
  )
import System.Environment (lookupEnv)
import System.IO (hFlush, stderr, stdout)
import Text.Megaparsec (Parsec, runParser, takeRest)
import Text.Megaparsec.Char (space)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf (printf)
import Text.Read (readEither)
import Prelude

defaultEdhConsoleSettings :: Settings IO
defaultEdhConsoleSettings =
  Settings
    { complete = \(_left, _right) -> return ("", []),
      historyFile = Nothing,
      autoAddHistory = True
    }

-- | This console serializes all out messages to 'stdout', all log messages
-- to 'stderr', through a 'TBQueue', so they don't mess up under concurrency.
--
-- Console input will wait the out queue being idle before prompting, this
-- is not perfect but better than otherwise more naive implementations.
--
-- Known issues:
--  *) still can mess up with others writing directly to 'stdout/stderr'
--  *) if all others use 'trace' only, there're minimum messups but emojis
--     seem to be break points
defaultEdhConsole :: Settings IO -> IO EdhConsole
defaultEdhConsole !inputSettings = do
  !envLogLevel <- lookupEnv "EDH_LOG_LEVEL"
  !outputTk <- newTMVarIO ()
  !logIdle <- newEmptyTMVarIO
  !outIdle <- newEmptyTMVarIO
  -- TODO detect backpressure from stdout/stderr, handle accordingly
  !ioQ <- newTQueueIO
  !logQueue <- newTQueueIO
  let logLevel = case envLogLevel of
        Nothing -> 20
        Just "DEBUG" -> 10
        Just "INFO" -> 20
        Just "WARN" -> 30
        Just "ERROR" -> 40
        Just "FATAL" -> 50
        Just ns -> case readEither ns of
          Left _ -> 0
          Right (ln :: Int) -> ln
      flushLogs :: IO ()
      flushLogs = atomically $ readTMVar logIdle
      logPrinter :: IO ()
      logPrinter = do
        !lr <-
          atomically (tryReadTQueue logQueue) >>= \case
            Just !lr -> do
              -- make sure log is marked busy
              void $ atomically $ tryTakeTMVar logIdle
              return lr
            Nothing -> do
              -- mark log idle
              void $ atomically $ tryPutTMVar logIdle ()
              -- block wait next log request
              !lr <- atomically $ readTQueue logQueue
              -- make sure log is marked busy
              void $ atomically $ tryTakeTMVar logIdle
              return lr
        bracket
          (atomically $ takeTMVar outputTk)
          (atomically . putTMVar outputTk)
          $ \() -> TIO.hPutStr stderr lr
        logPrinter
      logger :: EdhLogger
      logger !level !srcLoc !logPayload = do
        void $ tryTakeTMVar logIdle
        writeTQueue logQueue $! logPrefix <> logPayload <> "\n"
        where
          logPrefix :: Text
          logPrefix =
            ( case srcLoc of
                Nothing -> id
                Just !sl -> (<> sl <> "\n")
            )
              $ case level of
                _ | level >= 50 -> "🔥 "
                _ | level >= 40 -> "❗ "
                _ | level >= 30 -> "\x26A0\xFE0F  " --  ⚠️
                _ | level >= 20 -> "\x2139\xFE0F  " -- ℹ️
                _ | level >= 10 -> "🐞 "
                _ -> "😥 "
      ioLoop :: InputT IO ()
      ioLoop = do
        !ior <-
          liftIO $
            atomically (tryReadTQueue ioQ) >>= \case
              Just !ior -> do
                -- make sure out is marked busy
                void $ atomically $ tryTakeTMVar outIdle
                return ior
              Nothing -> do
                -- mark out idle
                void $ atomically $ tryPutTMVar outIdle ()
                -- block wait next i/o request
                !ior <- atomically $ readTQueue ioQ
                -- make sure out is marked busy
                void $ atomically $ tryTakeTMVar outIdle
                return ior
        case ior of
          ConsoleShutdown -> return () -- gracefully stop the io loop
          ConsoleOut !txt -> do
            liftIO $
              bracket
                (atomically $ takeTMVar outputTk)
                (atomically . putTMVar outputTk)
                $ \() -> do
                  TIO.hPutStr stdout txt
                  hFlush stdout
            ioLoop
          ConsoleIn !cmdIn !ps1 !ps2 -> do
            -- mark out idle before starting input, or flush request will hang
            -- up for user input
            liftIO $ atomically $ void $ tryPutTMVar outIdle ()
            readInput ps1 ps2 [] >>= \case
              Nothing ->
                -- reached EOF (end-of-feed) before clean shutdown
                liftIO $ TIO.hPutStrLn stderr "Your work may have lost, sorry."
              Just !cmd -> do
                -- got one piece of code
                liftIO $ atomically $ putTMVar cmdIn cmd
                ioLoop
        where
          readInput :: Text -> Text -> [Text] -> InputT IO (Maybe EdhInput)
          readInput !ps1 !ps2 !initialLines =
            handleInterrupt
              ( -- start over on Ctrl^C
                outputStrLn "" >> readLines []
              )
              $ withInterrupt $
                readLines initialLines
            where
              parsePasteSpec :: Parsec Void Text (Int, Int, Text)
              parsePasteSpec = do
                space
                lineCnt :: Int <- L.decimal
                space
                lineNo :: Int <- L.decimal
                space
                !srcName <- takeRest
                return (lineCnt, lineNo, srcName)
              recvPaste :: Text -> InputT IO (Maybe EdhInput)
              recvPaste !pasteSpec =
                case runParser parsePasteSpec "%%paste" pasteSpec of
                  Right (lineCnt, lineNo, srcName)
                    | lineCnt > 0 && lineNo > 0 ->
                      recvLines lineCnt [] >>= \case
                        Nothing -> return Nothing
                        Just !lines_ ->
                          return $
                            Just $
                              EdhInput
                                { edh'input'src'name = srcName,
                                  edh'input'1st'line = lineNo,
                                  edh'input'src'lines = lines_
                                }
                  _ ->
                    getInputLine
                      "Invalid %%paste spec\nKey in a valid one or Ctrl^C to cancel: "
                      >>= \case
                        Nothing -> return Nothing
                        Just !text ->
                          case T.stripPrefix "%%paste" (T.pack text) of
                            Nothing -> recvPaste ""
                            Just !pasteSpec' -> recvPaste pasteSpec'
              recvLines :: Int -> [Text] -> InputT IO (Maybe [Text])
              recvLines 0 !lines_ = return $ Just $ reverse lines_
              recvLines !n !lines_ =
                getPassword Nothing "" >>= \case
                  Nothing -> return Nothing
                  Just !line -> do
                    outputStr "\ESC[1A"
                    recvLines (n - 1) (T.pack line : lines_)
              readLines :: [Text] -> InputT IO (Maybe EdhInput)
              readLines !pendingLines =
                liftIO flushLogs >> getInputLine prompt >>= \case
                  Nothing -> case pendingLines of
                    [] -> return Nothing
                    _ ->
                      -- TODO warn about premature EOF ?
                      return Nothing
                  Just !text ->
                    let !code = T.pack text
                     in case pendingLines of
                          []
                            | "{" == T.stripEnd code ->
                              -- an unindented `{` marks start of multi-line input
                              readLines [""]
                          []
                            | "" == T.strip code ->
                              -- got an empty line in single-line input mode
                              readLines [] -- start over in single-line input mode
                          [] -> case T.stripPrefix "%%paste" code of
                            -- start pasting
                            Just !pasteSpec -> recvPaste pasteSpec
                            -- got a single line input
                            _ ->
                              return $
                                Just $
                                  EdhInput
                                    { edh'input'src'name = "",
                                      edh'input'1st'line = 1,
                                      edh'input'src'lines = [code]
                                    }
                          _ -> case T.stripEnd code of
                            "}" ->
                              -- an unindented `}` marks end of multi-line input
                              return $
                                Just $
                                  EdhInput "" 1 $
                                    reverse $
                                      init
                                        pendingLines
                            _ ->
                              -- got a line in multi-line input mode
                              readLines $ code : pendingLines
                where
                  prompt :: String
                  prompt = case pendingLines of
                    [] -> T.unpack ps1
                    _ -> T.unpack ps2 <> printf "%2d" (length pendingLines) <> ": "
  void $
    mask_ $
      forkIOWithUnmask $ \unmask ->
        finally (unmask logPrinter) $
          atomically $ do
            void $ tryPutTMVar outputTk ()
            void $ tryPutTMVar logIdle ()
            void $ tryPutTMVar outIdle ()
  return
    EdhConsole
      { consoleIO = atomically . writeTQueue ioQ,
        consoleIOLoop = flip finally flushLogs $ runInputT inputSettings ioLoop,
        consoleLogLevel = logLevel,
        consoleLogger = logger,
        consoleFlush = atomically $ void (readTMVar outIdle >> readTMVar logIdle)
      }

installEdhBatteries :: EdhWorld -> IO ()
installEdhBatteries world =
  void $
    runEdhProgram' world $ \ !ets -> do
      declareEdhOperators
        world
        "<batteries>"
        [ -- format: (symbol, precedence)

          -- annotations
          ("::", Infix, -9), -- attribute type annotation
          (":=:", Infix, -9), -- type synonym annotation
          ("!", InfixR, 0), -- free-form lhs annotation
          -- arrows, make it higher than (=), so an arrow procedure can be
          -- assigned to some attribute without quoting
          ("=>", InfixR, 1),
          ("=>*", InfixR, 1),
          -- branch
          ("->", InfixR, -1),
          -- catch
          ("$=>", InfixL, -2),
          -- finally
          ("@=>", InfixL, -2),
          -- the attribute key dereferencing operator
          ("@", InfixL, 10),
          -- attribute tempter,
          -- address an attribute off an object if possible, nil otherwise
          ("?", InfixL, 10),
          ("?@", InfixL, 10),
          -- the function application operator
          ("$", InfixR, -5), -- make it lower than procedure body definition
          -- (i.e. -3 to be cross checked with `parseProcBody`), or decorators
          -- can go wrong the flipped function application operator, in UNIX
          -- pipe semantics
          ("|", InfixL, 0), -- make it slightly higher than (->),
          -- so the guard syntax in pattern matching works nicely the flipped
          -- function application operator, in Haskell convention
          ("&", InfixL, -4), -- make it one higher than ($) as in Haskell
          -- assignments, make them lower than (++),
          -- so don't need to quote `a = b ++ c`
          ("=", InfixR, 0),
          ("?=", InfixR, 0),
          -- the definition operator, creates named value in Edh
          (":=", InfixR, 1),
          ("?:=", InfixR, 1),
          -- syntactic sugars for (=)
          ("++=", InfixR, 2),
          ("+=", InfixR, 2),
          ("-=", InfixR, 2),
          ("*=", InfixR, 2),
          ("/=", InfixR, 2),
          ("//=", InfixR, 2),
          ("%=", InfixR, 2),
          ("**=", InfixR, 2),
          ("&&=", InfixR, 3),
          ("||=", InfixR, 3),
          -- arithmetic
          ("+", InfixL, 6),
          ("-", InfixL, 6),
          ("*", InfixL, 7),
          ("/", InfixL, 7),
          ("//", InfixL, 7),
          ("%", InfixL, 7),
          ("**", InfixL, 8),
          -- comparations
          ("==", Infix, 4), -- deep-value-wise equality test
          ("!=", Infix, 4), -- inversed identity-wise equality test
          -- C style here, as (/=) is used for inplace division
          ("is not", Infix, 4), -- identity-wise negative equality test
          ("is", Infix, 4), -- identity-wise equality test
          (">", Infix, 4),
          (">=", Infix, 4),
          ("<", Infix, 4),
          ("<=", Infix, 4),
          -- logical/nullish boolean
          ("&&", InfixL, 3),
          ("||", InfixL, 3),
          ("and", InfixL, 3),
          ("or", InfixL, 3),
          -- comprehension
          --  * list comprehension:
          --     [] =< for x from range(100) do x*x
          --  * dict comprehension:
          --     {} =< for x from range(100) do (x, x*x)
          --  * args comprehension:
          --     () =< for x from range(100) do x*x
          ("=<", InfixL, 2),
          -- prepand to list
          --     l = [3,7,5]
          --     2 :> l
          --     [2,3,7,5]
          (":>", InfixR, 2),
          -- the pair constructor, creates pairs in Edh
          (":", InfixL, 2),
          -- reverse left-list and prepend to right-list
          --     l = [3,7,5]
          --     [9,2] >> l
          --     [2,9,3,7,5]
          (">>", InfixR, 2),
          -- element-of test
          ("?<=", Infix, 4),
          -- prefix test
          ("|*", Infix, 4),
          -- suffix test
          ("*|", Infix, 4),
          -- prefix cut (pattern only)
          (">@", InfixL, 3),
          -- suffix cut (pattern only)
          ("@<", InfixL, 3),
          -- publish to sink
          --     evsPub <- outEvent
          ("<-", InfixR, 1),
          -- string coercing concatenation
          ("++", InfixL, 2),
          -- logging
          ("<|", Infix, 1)
        ]

      -- global operators at world root scope
      !basicOperators <-
        sequence
          [ (AttrByName sym,) <$> mkIntrinsicOp world sym iop
            | (sym, iop) <-
                [ ("@", attrDerefAddrProc),
                  ("$", fapProc),
                  ("|", ffapProc),
                  ("&", ffapProc),
                  (":=", defProc),
                  ("?:=", defMissingProc),
                  (":", pairCtorProc),
                  ("?", attrTemptProc),
                  ("?@", attrDerefTemptProc),
                  ("++", concatProc),
                  ("=<", cprhProc),
                  ("?<=", elemProc),
                  ("|*", isPrefixOfProc),
                  ("*|", hasSuffixProc),
                  (":>", prpdProc),
                  (">>", lstrvrsPrpdProc),
                  ("<-", evtPubProc),
                  ("+", addProc),
                  ("-", subtProc),
                  ("*", mulProc),
                  ("/", divProc),
                  ("//", divIntProc),
                  ("%", modIntProc),
                  ("**", powProc),
                  ("&&", logicalAndProc),
                  ("||", logicalOrProc),
                  ("and", nullishAndProc),
                  ("or", nullishOrProc),
                  ("==", valEqProc id),
                  ("!=", valEqProc not),
                  ("is not", idNotEqProc),
                  ("is", idEqProc),
                  (">", isGtProc),
                  (">=", isGeProc),
                  ("<", isLtProc),
                  ("<=", isLeProc),
                  ("=", assignProc),
                  ("++=", assignWithOpProc "++"),
                  ("+=", assignWithOpProc "+"),
                  ("-=", assignWithOpProc "-"),
                  ("*=", assignWithOpProc "*"),
                  ("/=", assignWithOpProc "/"),
                  ("//=", assignWithOpProc "//"),
                  ("%=", assignWithOpProc "%"),
                  ("**=", assignWithOpProc "**"),
                  ("&&=", assignWithOpProc "&&"),
                  ("||=", assignWithOpProc "||"),
                  ("?=", assignMissingProc),
                  ("=>", arrowProc),
                  ("=>*", prodArrowProc),
                  ("->", branchProc),
                  ("$=>", catchProc),
                  ("@=>", finallyProc),
                  ("::", attrAnnoProc),
                  (":=:", typeAnnoProc),
                  ("!", lhsFreeFormAnnoProc),
                  ("<|", loggingProc)
                ]
          ]

      -- global procedures at world root scope
      !basicProcs <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope mc nm hp
            | (mc, nm, hp) <-
                [ (EdhMethod, "__StringType_bytes__", wrapHostProc strEncodeProc),
                  (EdhMethod, "__BlobType_utf8string__", wrapHostProc blobDecodeProc),
                  (EdhMethod, "__DecimalType_trunc__", wrapHostProc decTruncProc),
                  (EdhMethod, "__DecimalType_round__", wrapHostProc decRoundProc),
                  (EdhMethod, "UUID", wrapHostProc uuidCtorProc),
                  (EdhMethod, "error", wrapHostProc errorProc),
                  (EdhMethod, "id", wrapHostProc idProc),
                  (EdhMethod, "blob", wrapHostProc blobProc),
                  (EdhMethod, "str", wrapHostProc strProc),
                  (EdhMethod, "json", (jsonProc, WildReceiver)),
                  (EdhMethod, "repr", wrapHostProc reprProc),
                  (EdhMethod, "cap", wrapHostProc capProc),
                  (EdhMethod, "grow", wrapHostProc growProc),
                  (EdhMethod, "len", wrapHostProc lenProc),
                  (EdhMethod, "mark", wrapHostProc markProc),
                  (EdhMethod, "show", wrapHostProc showProc),
                  (EdhMethod, "desc", wrapHostProc descProc),
                  (EdhMethod, "dict", wrapHostProc dictProc),
                  (EdhMethod, "null", wrapHostProc isNullProc),
                  (EdhMethod, "compare", wrapHostProc cmpProc),
                  (EdhMethod, "type", wrapHostProc typeProc),
                  (EdhMethod, "__IntrinsicType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__MethodType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__HostMethodType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__OperatorType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__HostOperType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__GeneratorType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__HostGenrType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__InterpreterType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__ProducerType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "__DescriptorType_name__", wrapHostProc procNameProc),
                  (EdhMethod, "property", wrapHostProc propertyProc),
                  (EdhMethod, "setter", wrapHostProc setterProc),
                  (EdhMethod, "constructor", wrapHostProc ctorProc),
                  (EdhMethod, "supers", wrapHostProc supersProc),
                  (EdhMethod, "parseEdh", wrapHostProc parseEdhProc),
                  (EdhMethod, "makeOp", wrapHostProc makeOpProc),
                  (EdhMethod, "__SinkType_subseq__", wrapHostProc sink'subseqProc),
                  (EdhMethod, "__SinkType_mrv__", wrapHostProc sink'mrvProc),
                  (EdhMethod, "__SinkType_eos__", wrapHostProc sink'eosProc),
                  (EdhMethod, "__DictType_size__", wrapHostProc dictSizeProc),
                  (EdhMethod, "__DictType_keys__", wrapHostProc dictKeysProc),
                  (EdhMethod, "__DictType_values__", wrapHostProc dictValuesProc),
                  (EdhMethod, "__ListType_push__", wrapHostProc listPushProc),
                  (EdhMethod, "__ListType_pop__", wrapHostProc listPopProc)
                ]
          ]
            ++ [(AttrByName "Vector",) . EdhObject <$> createVectorClass rootScope]

      !console <- createNamespace world "console" []
      !conScope <- objectScope console
      !conMths <-
        sequence
          [ (AttrByName nm,) <$> mkHostProc conScope vc nm hp
            | (vc, nm, hp) <-
                [ (EdhMethod, "exit", wrapHostProc conExitProc),
                  (EdhMethod, "readSource", wrapHostProc conReadSourceProc),
                  (EdhMethod, "readCommand", wrapHostProc conReadCommandProc),
                  (EdhMethod, "log", wrapHostProc conLogProc),
                  (EdhMethod, "print", wrapHostProc conPrintProc),
                  (EdhMethod, "now", wrapHostProc conNowProc),
                  (EdhGnrtor, "everyMicros", wrapHostProc conEveryMicrosProc),
                  (EdhGnrtor, "everyMillis", wrapHostProc conEveryMillisProc),
                  (EdhGnrtor, "everySeconds", wrapHostProc conEverySecondsProc)
                ]
          ]
      let !conArts =
            conMths
              ++ [ (AttrByName "debug", EdhDecimal 10),
                   (AttrByName "info", EdhDecimal 20),
                   (AttrByName "warn", EdhDecimal 30),
                   (AttrByName "error", EdhDecimal 40),
                   (AttrByName "fatal", EdhDecimal 50),
                   ( AttrByName "logLevel",
                     EdhDecimal
                       (fromIntegral $ consoleLogLevel $ edh'world'console world)
                   )
                 ]
      !conExps <-
        EdhDict
          <$> createEdhDict [(attrKeyValue k, v) | (k, v) <- conArts]
      flip iopdUpdate (edh'scope'entity conScope) $
        conArts
          ++ [(AttrByName "__exports__", conExps)]

      -- artifacts considered safe for sandboxed envs, to afford basic Edh
      -- source evaluation
      let !basicArts = basicOperators ++ basicProcs

      -- artifacts considered privileged, thus not made available to sandboxed
      -- envs
      !privilegedProcs <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope mc nm hp
            | (mc, nm, hp) <- [(EdhMethod, "sandbox", wrapHostProc sandboxProc)]
          ]
      let !privilegedArts =
            (AttrByName "console", EdhObject console) : privilegedProcs
      iopdUpdate (basicArts ++ privilegedArts) rootEntity
      runEdhTx ets $
        importEdhModule' rootEntity WildReceiver "batteries/root" endOfEdh

      iopdUpdate basicArts sandboxEntity
      runEdhTx ets $
        importEdhModule' sandboxEntity WildReceiver "batteries/sandbox" endOfEdh
  where
    !rootScope = edh'world'root world
    !rootEntity = edh'scope'entity rootScope

    !sandboxScope = edh'world'sandbox world
    !sandboxEntity = edh'scope'entity sandboxScope

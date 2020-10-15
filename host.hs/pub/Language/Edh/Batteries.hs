
module Language.Edh.Batteries
  ( defaultEdhConsoleSettings
  , defaultEdhConsole
  , installEdhBatteries
  , module Language.Edh.Batteries.Data
  , module Language.Edh.Batteries.Math
  , module Language.Edh.Batteries.Assign
  , module Language.Edh.Batteries.Reflect
  , module Language.Edh.Batteries.Ctrl
  , module Language.Edh.Batteries.Console
  , module Language.Edh.Batteries.Evt
  , module Language.Edh.Batteries.Vector
  )
where

import           Prelude

import           Text.Printf

import           System.IO                      ( stderr )
import           System.Environment
import           Text.Read

import           Control.Exception

import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as TIO

import           System.Console.Haskeline       ( InputT
                                                , Settings(..)
                                                , runInputT
                                                , outputStr
                                                , outputStrLn
                                                , getInputLine
                                                , getPassword
                                                , handleInterrupt
                                                , withInterrupt
                                                )
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Language.Edh.Runtime
import           Language.Edh.InterOp

import           Language.Edh.Batteries.Data
import           Language.Edh.Batteries.Math
import           Language.Edh.Batteries.Assign
import           Language.Edh.Batteries.Reflect
import           Language.Edh.Batteries.Ctrl
import           Language.Edh.Batteries.Console
import           Language.Edh.Batteries.Evt
import           Language.Edh.Batteries.Vector

import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


defaultEdhConsoleSettings :: Settings IO
defaultEdhConsoleSettings = Settings
  { complete       = \(_left, _right) -> return ("", [])
  , historyFile    = Nothing
  , autoAddHistory = True
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
  envLogLevel <- lookupEnv "EDH_LOG_LEVEL"
  logIdle     <- newEmptyTMVarIO
  outIdle     <- newEmptyTMVarIO
  ioQ         <- newTBQueueIO 100
  logQueue    <- newTBQueueIO 100
  let
    logLevel = case envLogLevel of
      Nothing      -> 20
      Just "DEBUG" -> 10
      Just "INFO"  -> 20
      Just "WARN"  -> 30
      Just "ERROR" -> 40
      Just "FATAL" -> 50
      Just ns      -> case readEither ns of
        Left  _           -> 0
        Right (ln :: Int) -> ln
    flushLogs :: IO ()
    flushLogs = atomically $ readTMVar logIdle
    logPrinter :: IO ()
    logPrinter = do
      lr <- atomically (tryReadTBQueue logQueue) >>= \case
        Just !lr -> do
          void $ atomically $ tryTakeTMVar logIdle
          return lr
        Nothing -> do
          void $ atomically $ tryPutTMVar logIdle ()
          lr <- atomically $ readTBQueue logQueue
          void $ atomically $ tryTakeTMVar logIdle
          return lr
      TIO.hPutStr stderr lr
      logPrinter
    logger :: EdhLogger
    logger !level !srcLoc !logArgs = do
      void $ tryTakeTMVar logIdle
      case logArgs of
        ArgsPack [!argVal] !kwargs | odNull kwargs ->
          writeTBQueue logQueue $! T.pack logPrefix <> logString argVal <> "\n"
        _ -> -- todo: format structured log record,
             -- with some log parsers in mind
          writeTBQueue logQueue $! T.pack (logPrefix ++ show logArgs) <> "\n"
     where
      logString :: EdhValue -> Text
      logString (EdhString s) = s
      logString v             = T.pack $ show v
      logPrefix :: String
      logPrefix =
        (case srcLoc of
            Nothing -> id
            Just sl -> (++ sl ++ "\n")
          )
          $ case level of
              _ | level >= 50 -> "🔥 "
              _ | level >= 40 -> "❗ "
              _ | level >= 30 -> "⚠️ "
              _ | level >= 20 -> "ℹ️ "
              _ | level >= 10 -> "🐞 "
              _               -> "😥 "
    ioLoop :: InputT IO ()
    ioLoop = do
      ior <- liftIO $ atomically (tryReadTBQueue ioQ) >>= \case
        Just !ior -> do
          void $ atomically $ tryTakeTMVar outIdle
          return ior
        Nothing -> do
          void $ atomically $ tryPutTMVar outIdle ()
          ior <- atomically $ readTBQueue ioQ
          void $ atomically $ tryTakeTMVar outIdle
          return ior
      case ior of
        ConsoleShutdown -> return () -- gracefully stop the io loop
        ConsoleOut !txt -> do
          outputStr $ T.unpack txt
          ioLoop
        ConsoleIn !cmdIn !ps1 !ps2 -> readInput ps1 ps2 [] >>= \case
          Nothing -> -- reached EOF (end-of-feed) before clean shutdown
            liftIO $ TIO.hPutStrLn stderr "Your work may have lost, sorry."
          Just !cmd -> do -- got one piece of code
            liftIO $ atomically $ putTMVar cmdIn cmd
            ioLoop
     where
        -- | The repl line reader
      readInput :: Text -> Text -> [Text] -> InputT IO (Maybe EdhInput)
      readInput !ps1 !ps2 !initialLines =
        handleInterrupt ( -- start over on Ctrl^C
                         outputStrLn "" >> readLines [])
          $ withInterrupt
          $ readLines initialLines
       where
        parsePasteSpec :: Parsec Void Text (Int, Int, Text)
        parsePasteSpec = do
          space
          lineCnt :: Int <- L.decimal
          space
          lineNo :: Int <- L.decimal
          space
          srcName <- takeRest
          return (lineCnt, lineNo, srcName)
        recvPaste :: Text -> InputT IO (Maybe EdhInput)
        recvPaste !pasteSpec =
          case runParser parsePasteSpec "%%paste" pasteSpec of
            Right (lineCnt, lineNo, srcName) | lineCnt > 0 && lineNo > 0 ->
              recvLines lineCnt [] >>= \case
                Nothing      -> return Nothing
                Just !lines_ -> return $ Just $ EdhInput
                  { edh'input'src'name  = srcName
                  , edh'input'1st'line  = lineNo
                  , edh'input'src'lines = lines_
                  }
            _ ->
              getInputLine
                  "Invalid %%paste spec\nKey in a valid one or Ctrl^C to cancel: "
                >>= \case
                      Nothing -> return Nothing
                      Just !text ->
                        case T.stripPrefix "%%paste" (T.pack text) of
                          Nothing          -> recvPaste ""
                          Just !pasteSpec' -> recvPaste pasteSpec'
        recvLines :: Int -> [Text] -> InputT IO (Maybe [Text])
        recvLines 0  !lines_ = return $ Just $ reverse lines_
        recvLines !n !lines_ = getPassword Nothing "" >>= \case
          Nothing    -> return Nothing
          Just !line -> do
            outputStr "\ESC[1A"
            recvLines (n - 1) (T.pack line : lines_)
        readLines :: [Text] -> InputT IO (Maybe EdhInput)
        readLines !pendingLines =
          liftIO flushLogs >> getInputLine prompt >>= \case
            Nothing -> case pendingLines of
              [] -> return Nothing
              _ -> -- TODO warn about premature EOF ?
                return Nothing
            Just !text ->
              let !code = T.pack text
              in  case pendingLines of
                    [] | "{" == T.stripEnd code ->
                      -- an unindented `{` marks start of multi-line input
                      readLines [""]
                    [] | "" == T.strip code ->
                      -- got an empty line in single-line input mode
                      readLines [] -- start over in single-line input mode
                    [] -> case T.stripPrefix "%%paste" code of
                      -- start pasting
                      Just !pasteSpec -> recvPaste pasteSpec
                      -- got a single line input
                      _               -> return $ Just $ EdhInput
                        { edh'input'src'name  = ""
                        , edh'input'1st'line  = 1
                        , edh'input'src'lines = [code]
                        }
                    _ -> case T.stripEnd code of
                      "}" -> -- an unindented `}` marks end of multi-line input
                             return $ Just $ EdhInput "" 1 $ reverse $ init
                        pendingLines
                      _ -> -- got a line in multi-line input mode
                        readLines $ code : pendingLines
         where
          prompt :: String
          prompt = case pendingLines of
            [] -> T.unpack ps1
            _  -> T.unpack ps2 <> printf "%2d" (length pendingLines) <> ": "
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    finally (unmask logPrinter) $ atomically $ do
      void $ tryPutTMVar logIdle ()
      void $ tryPutTMVar outIdle ()
  return EdhConsole
    { consoleIO       = ioQ
    , consoleIOLoop   = flip finally flushLogs $ runInputT inputSettings ioLoop
    , consoleLogLevel = logLevel
    , consoleLogger   = logger
    , consoleFlush = atomically $ void (readTMVar outIdle >> readTMVar logIdle)
    }


installEdhBatteries :: MonadIO m => EdhWorld -> m ()
installEdhBatteries world =
  liftIO $ void $ runEdhProgram' (worldContext world) $ \ !ets -> do

      -- TODO survey for best practices & advices on precedences here
      --      once it's declared, can not be changed in the world.

    declareEdhOperators
      world
      "<batteries>"
      [ -- format: (symbol, precedence)

        -- annotations
        ("::", -9)
      , ( "!"
        , 0
        )

        -- arrow, make it higher than (=), so an arrow procedure can be
        -- assigned to some attribute without quoting
      , ( "=>"
        , 1
        )
        -- branch
      , ( "->"
        , -1
        )
        -- catch
      , ( "$=>"
        , -2
        )
        -- finally
      , ( "@=>"
        , -2
        )

      -- the attribute key dereferencing operator
      , ( "@"
        , 10
        )
      -- attribute tempter, 
      -- address an attribute off an object if possible, nil otherwise
      , ("?", 10)
      , ( "?@"
        , 10
        )

      -- the function application operator
      , ( "$"
        , -5 -- make it lower than procedure body definition (i.e. -3 to be
        -- cross checked with `parseProcBody`), or decorators can go wrong
        )
      -- the flipped function application operator, in UNIX pipe semantics
      , ( "|"
        , 0 -- make it slightly higher than (->),
            -- so the guard syntax in pattern matching works nicely
        )
      -- the flipped function application operator, in Haskell convention
      , ( "&"
        , -4 -- make it one higher than ($) as in Haskell
        )

      -- assignments, make them lower than (++),
      -- so don't need to quote `a = b ++ c`
      , ("=", 0)
      , ( "?="
        , 0
        )
      -- the definition operator, creates named value in Edh
      , (":=", 1)
      , ( "?:="
        , 1
        )

      -- syntactic sugars for (=)
      , ("++=", 2)
      , ("+=" , 2)
      , ("-=" , 2)
      , ("*=" , 2)
      , ("/=" , 2)
      , ("//=", 2)
      , ("%=" , 2)
      , ( "**="
        , 2
        )

      -- arithmetic
      , ("+" , 6)
      , ("-" , 6)
      , ("*" , 7)
      , ("/" , 7)
      , ("//", 7)
      , ("%" , 7)
      , ( "**"
        , 8
        )
      -- comparations
      , ( "=="
        , 4
        ) -- deep-value-wise equality test
      , ( "!="
        , 4
        ) -- inversed identity-wise equality test
          -- C style here, as (/=) is used for inplace division
      , ( "is not"
        , 4
        ) -- identity-wise negative equality test
      , ( "is"
        , 4
        ) -- identity-wise equality test
      , (">" , 4)
      , (">=", 4)
      , ("<" , 4)
      , ( "<="
        , 4
        )
        -- logical arithmetic
      , ("&&" , 3)
      , ("||" , 3)
      , ("&&=", 3)
      , ( "||="
        , 3
        )

        -- emulate the ternary operator in C:
        --       onCnd ? oneThing : theOther
        --  * Python
        --       onCnd and oneThing or theOther
        --  * Edh
        --       onCnd &> oneThing |> theOther
      , ("&>", 3)
      , ( "|>"
        , 3
        )

        -- comprehension
        --  * list comprehension:
        --     [] =< for x from range(100) do x*x
        --  * dict comprehension:
        --     {} =< for x from range(100) do (x, x*x)
        --  * tuple comprehension:
        --     (,) =< for x from range(100) do x*x
      , ( "=<"
        , 2
        )
        -- prepand to list
        --     l = [3,7,5]
        --     2 :> l
        --     [2,3,7,5]
      , ( ":>"
        , 2
        )
      -- the pair constructor, creates pairs in Edh
      , ( ":"
        , 2
        )
        -- reverse left-list and prepend to right-list
        --     l = [3,7,5]
        --     [9,2] >> l
        --     [2,9,3,7,5]
      , ( ">>"
        , 2
        )
        -- element-of test
      , ( "?<="
        , 3
        )
        -- prefix test
      , ( "|*"
        , 3
        )
        -- suffix test
      , ( "*|"
        , 3
        )
        -- prefix cut (pattern only)
      , ( ">@"
        , 3
        )
        -- suffix cut (pattern only)
      , ( "@<"
        , 3
        )

        -- publish to sink
        --     evsPub <- outEvent
      , ( "<-"
        , 1
        )

        -- string coercing concatenation
      , ( "++"
        , 2
        )

        -- logging
      , ("<|", 1)
      ]

    -- global operators at world root scope
    !rootOperators <- sequence
      [ (AttrByName sym, ) <$> mkIntrinsicOp world sym iop
      | (sym, iop) <-
        [ ("@"     , attrDerefAddrProc)
        , ("$"     , fapProc)
        , ("|"     , ffapProc)
        , ("&"     , ffapProc)
        , (":="    , defProc)
        , ("?:="   , defMissingProc)
        , (":"     , pairCtorProc)
        , ("?"     , attrTemptProc)
        , ("?@"    , attrDerefTemptProc)
        , ("++"    , concatProc)
        , ("=<"    , cprhProc)
        , ("?<="   , elemProc)
        , ("|*"    , isPrefixOfProc)
        , ("*|"    , hasSuffixProc)
        , (":>"    , prpdProc)
        , (">>"    , lstrvrsPrpdProc)
        , ("<-"    , evtPubProc)
        , ("+"     , addProc)
        , ("-"     , subtProc)
        , ("*"     , mulProc)
        , ("/"     , divProc)
        , ("//"    , divIntProc)
        , ("%"     , modIntProc)
        , ("**"    , powProc)
        , ("&&"    , logicalAndProc)
        , ("||"    , logicalOrProc)
        , ("=="    , valEqProc id)
        , ("!="    , valEqProc not)
        , ("is not", idNotEqProc)
        , ("is"    , idEqProc)
        , (">"     , isGtProc)
        , (">="    , isGeProc)
        , ("<"     , isLtProc)
        , ("<="    , isLeProc)
        , ("="     , assignProc)
        , ("++="   , assignWithOpProc "++")
        , ("+="    , assignWithOpProc "+")
        , ("-="    , assignWithOpProc "-")
        , ("*="    , assignWithOpProc "*")
        , ("/="    , assignWithOpProc "/")
        , ("//="   , assignWithOpProc "//")
        , ("%="    , assignWithOpProc "%")
        , ("**="   , assignWithOpProc "**")
        , ("&&="   , assignWithOpProc "&&")
        , ("||="   , assignWithOpProc "||")
        , ("?="    , assignMissingProc)
        , ("=>"    , arrowProc)
        , ("->"    , branchProc)
        , ("$=>"   , catchProc)
        , ("@=>"   , finallyProc)
        , ("::"    , silentAnnoProc)
        , ("!"     , leftAnnoProc)
        , ("<|"    , loggingProc)
        ]
      ]

    -- global procedures at world root scope
    !rootProcs <-
      sequence
      $  [ (AttrByName nm, ) <$> mkHostProc rootScope mc nm hp
         | (mc, nm, hp) <-
           [ (EdhMethod, "__StringType_bytes__"    , wrapHostProc strEncodeProc)
           , (EdhMethod, "__BlobType_utf8string__", wrapHostProc blobDecodeProc)
           , (EdhMethod, "Symbol", wrapHostProc symbolCtorProc)
           , (EdhMethod, "UUID"                    , wrapHostProc uuidCtorProc)
           , (EdhMethod, "__ArgsPackType_args__"   , wrapHostProc apkArgsProc)
           , (EdhMethod, "__ArgsPackType_kwargs__" , wrapHostProc apkKwrgsProc)
           , (EdhMethod, "error"                   , wrapHostProc errorProc)
           , (EdhMethod, "id"                      , wrapHostProc idProc)
           , (EdhMethod, "blob"                    , wrapHostProc blobProc)
           , (EdhMethod, "str"                     , wrapHostProc strProc)
           , (EdhMethod, "repr"                    , wrapHostProc reprProc)
           , (EdhMethod, "cap"                     , wrapHostProc capProc)
           , (EdhMethod, "grow"                    , wrapHostProc growProc)
           , (EdhMethod, "len"                     , wrapHostProc lenProc)
           , (EdhMethod, "mark"                    , wrapHostProc markProc)
           , (EdhMethod, "show"                    , wrapHostProc showProc)
           , (EdhMethod, "desc"                    , wrapHostProc descProc)
           , (EdhMethod, "dict"                    , wrapHostProc dictProc)
           , (EdhMethod, "null"                    , wrapHostProc isNullProc)
           , (EdhMethod, "type"                    , wrapHostProc typeProc)
           , (EdhMethod, "__IntrinsicType_name__"  , wrapHostProc procNameProc)
           , (EdhMethod, "__MethodType_name__"     , wrapHostProc procNameProc)
           , (EdhMethod, "__HostMethodType_name__" , wrapHostProc procNameProc)
           , (EdhMethod, "__OperatorType_name__"   , wrapHostProc procNameProc)
           , (EdhMethod, "__HostOperType_name__"   , wrapHostProc procNameProc)
           , (EdhMethod, "__GeneratorType_name__"  , wrapHostProc procNameProc)
           , (EdhMethod, "__HostGenrType_name__"   , wrapHostProc procNameProc)
           , (EdhMethod, "__InterpreterType_name__", wrapHostProc procNameProc)
           , (EdhMethod, "__ProducerType_name__"   , wrapHostProc procNameProc)
           , (EdhMethod, "__DescriptorType_name__" , wrapHostProc procNameProc)
           , (EdhMethod, "property"                , wrapHostProc propertyProc)
           , (EdhMethod, "setter"                  , wrapHostProc setterProc)
           , (EdhMethod, "constructor"             , wrapHostProc ctorProc)
           , (EdhMethod, "supers"                  , wrapHostProc supersProc)
           , (EdhMethod, "makeOp"                  , wrapHostProc makeOpProc)
           , (EdhMethod, "__SinkType_mrv__"        , wrapHostProc sink'mrvProc)
           , (EdhMethod, "__SinkType_eos__"        , wrapHostProc sink'eosProc)
           , (EdhMethod, "__DictType_size__"       , wrapHostProc dictSizeProc)
           , (EdhMethod, "__ListType_push__"       , wrapHostProc listPushProc)
           , (EdhMethod, "__ListType_pop__"        , wrapHostProc listPopProc)
           ]
         ]
      ++ [(AttrByName "Vector", ) . EdhObject <$> createVectorClass rootScope]


    !console <- createNamespace
      world
      "console"
      [ (AttrByName "debug", EdhDecimal 10)
      , (AttrByName "info" , EdhDecimal 20)
      , (AttrByName "warn" , EdhDecimal 30)
      , (AttrByName "error", EdhDecimal 40)
      , (AttrByName "fatal", EdhDecimal 50)
      , ( AttrByName "logLevel"
        , EdhDecimal (fromIntegral $ consoleLogLevel $ edh'world'console world)
        )
      ]
    !conScope <- objectScope console

    !conArts  <- sequence
      [ (AttrByName nm, ) <$> mkHostProc conScope vc nm hp
      | (vc, nm, hp) <-
        [ (EdhMethod, "exit"        , wrapHostProc conExitProc)
        , (EdhMethod, "readSource"  , wrapHostProc conReadSourceProc)
        , (EdhMethod, "readCommand" , wrapHostProc conReadCommandProc)
        , (EdhMethod, "print"       , wrapHostProc conPrintProc)
        , (EdhMethod, "now"         , wrapHostProc conNowProc)
        , (EdhGnrtor, "everyMicros" , wrapHostProc conEveryMicrosProc)
        , (EdhGnrtor, "everyMillis" , wrapHostProc conEveryMillisProc)
        , (EdhGnrtor, "everySeconds", wrapHostProc conEverySecondsProc)
        ]
      ]
    iopdUpdate conArts $ edh'scope'entity conScope

    flip iopdUpdate rootEntity
      $  rootOperators
      ++ rootProcs
      ++ [
          -- console module
          (AttrByName "console", EdhObject console)
          --
                                                   ]

    -- import the parts written in Edh 
    runEdhTx ets
      $ importEdhModule' rootEntity WildReceiver "batteries/root" endOfEdh

 where

  !rootScope  = edh'world'root world
  !rootEntity = edh'scope'entity rootScope

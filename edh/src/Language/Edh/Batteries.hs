
module Language.Edh.Batteries where

import           Prelude

import           Text.Printf

import           System.IO                      ( stderr )
import           System.Environment
import           Text.Read

import           Control.Exception

import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
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

import           Data.Lossless.Decimal         as D

import           Language.Edh.Runtime

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
installEdhBatteries world = liftIO $ do
  conClassUniq <- newUnique
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do

      -- TODO survey for best practices & advices on precedences here
      --      once it's declared, can not be changed in the world.

      declareEdhOperators
        world
        "<batteries>"
        [ -- format: (symbol, precedence)

          -- annotation
          ( "::"
          , -9
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
          , -5
          )
        -- the flipped function application operator, a.k.a pipe operator
        , ( "|"
          , -5
          )

        -- assignments, make it lower than (++), so don't need to quote `a = b ++ c`
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
          --     2 => l
          --     [2,3,7,5]
        , ( "=>"
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
          , ("=>"    , prpdProc)
          , (">>"    , lstrvrsPrpdProc)
          , ("<-"    , evtPubProc)
          , ("+"     , addProc)
          , ("-"     , subsProc)
          , ("*"     , mulProc)
          , ("/"     , divProc)
          , ("//"    , divIntProc)
          , ("%"     , modIntProc)
          , ("**"    , powProc)
          , ("&&"    , logicalAndProc)
          , ("||"    , logicalOrProc)
          , ("=="    , valEqProc)
          , ("is not", idNotEqProc)
          , ("is"    , idEqProc)
          , ("!="    , idNeProc)
          , (">"     , isGtProc)
          , (">="    , isGeProc)
          , ("<"     , isLtProc)
          , ("<="    , isLeProc)
          , ("="     , assignProc)
          , ("+="    , assignWithOpProc "+" addProc)
          , ("-="    , assignWithOpProc "-" subsProc)
          , ("*="    , assignWithOpProc "*" mulProc)
          , ("/="    , assignWithOpProc "/" divProc)
          , ("//="   , assignWithOpProc "//" divIntProc)
          , ("%="    , assignWithOpProc "%" modIntProc)
          , ("**="   , assignWithOpProc "**" powProc)
          , ("&&="   , assignWithOpProc "&&" logicalAndProc)
          , ("||="   , assignWithOpProc "||" logicalOrProc)
          , ("?="    , assignMissingProc)
          , ("->"    , branchProc)
          , ("$=>"   , catchProc)
          , ("@=>"   , finallyProc)
          , ("::"    , annoProc)
          , ("<|"    , loggingProc)
          ]
        ]

      -- global procedures at world root scope
      !rootProcs <-
        sequence
        $  [ (AttrByName nm, ) <$> mkHostProc rootScope mc nm hp args
           | (mc, nm, hp, args) <-
             [ ( EdhMethod
               , "__StringType_bytes__"
               , strEncodeProc
               , PackReceiver [mandatoryArg "str"]
               )
             , ( EdhMethod
               , "__BlobType_utf8string__"
               , blobDecodeProc
               , PackReceiver [mandatoryArg "blob"]
               )
             , ( EdhMethod
               , "Symbol"
               , symbolCtorProc
               , PackReceiver [mandatoryArg "repr", RecvRestPosArgs "reprs"]
               )
             , ( EdhMethod
               , "UUID"
               , uuidCtorProc
               , PackReceiver [mandatoryArg "uuidText"]
               )
             , ( EdhMethod
               , "__ArgsPackType_args__"
               , apkArgsProc
               , PackReceiver [mandatoryArg "apk"]
               )
             , ( EdhMethod
               , "__ArgsPackType_kwargs__"
               , apkKwrgsProc
               , PackReceiver [mandatoryArg "apk"]
               )
             , (EdhMethod, "repr", reprProc, WildReceiver)
             , ( EdhMethod
               , "cap"
               , capProc
               , PackReceiver [mandatoryArg "container"]
               )
             , ( EdhMethod
               , "grow"
               , growProc
               , PackReceiver
                 [mandatoryArg "container", mandatoryArg "newCapacity"]
               )
             , ( EdhMethod
               , "len"
               , lenProc
               , PackReceiver [mandatoryArg "container"]
               )
             , ( EdhMethod
               , "mark"
               , markProc
               , PackReceiver
                 [mandatoryArg "container", mandatoryArg "newLength"]
               )
             , (EdhMethod, "show", showProc, PackReceiver [mandatoryArg "val"])
             , (EdhMethod, "desc", descProc, PackReceiver [mandatoryArg "val"])
             , (EdhMethod, "dict", dictProc  , WildReceiver)
             , (EdhMethod, "null", isNullProc, WildReceiver)
             , (EdhMethod, "type", typeProc  , WildReceiver)
             , ( EdhMethod
               , "__IntrinsicType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__ClassType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__HostClassType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__MethodType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__HostMethodType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__OperatorType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__HostOperType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__GeneratorType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "__HostGenrType_name__"
               , procNameProc
               , PackReceiver [mandatoryArg "p"]
               )
             , ( EdhMethod
               , "property"
               , propertyProc
               , PackReceiver
                 [ mandatoryArg "getter"
                 , optionalArg "setter" $ LitExpr NilLiteral
                 ]
               )
             , ( EdhMethod
               , "setter"
               , setterProc
               , PackReceiver [mandatoryArg "mth"]
               )
             , (EdhMethod, "constructor", ctorProc       , WildReceiver)
             , (EdhMethod, "supers"     , supersProc     , WildReceiver)
             , (EdhMethod, "scope"      , scopeObtainProc, PackReceiver [])
             , ( EdhMethod
               , "makeOp"
               , makeOpProc
               , PackReceiver
                 [mandatoryArg "lhe", mandatoryArg "opSym", mandatoryArg "rhe"]
               )
             , (EdhMethod, "mre", mreProc, PackReceiver [mandatoryArg "evs"])
             , (EdhMethod, "eos", eosProc, PackReceiver [mandatoryArg "evs"])
             , ( EdhMethod
               , "__DictType_size__"
               , dictSizeProc
               , PackReceiver [mandatoryArg "d"]
               )
             , ( EdhMethod
               , "__ListType_push__"
               , listPushProc
               , PackReceiver [mandatoryArg "l"]
               )
             , ( EdhMethod
               , "__ListType_pop__"
               , listPopProc
               , PackReceiver [mandatoryArg "l"]
               )
             ]
           ]
        ++ [ ((AttrByName nm, ) <$>)
             $   mkHostClass rootScope nm hc
             =<< createSideEntityManipulater True
             =<< mths pgs
           | (nm, hc, mths) <- [("Vector", vecHostCtor, vecMethods)]
           ]


      !conEntity <- createHashEntity =<< iopdFromList
        [ (AttrByName "__repr__", EdhString "<console>")
        , (AttrByName "debug"   , EdhDecimal 10)
        , (AttrByName "info"    , EdhDecimal 20)
        , (AttrByName "warn"    , EdhDecimal 30)
        , (AttrByName "error"   , EdhDecimal 40)
        , (AttrByName "fatal"   , EdhDecimal 50)
        , ( AttrByName "logLevel"
          , EdhDecimal (fromIntegral $ consoleLogLevel $ worldConsole world)
          )
        ]
      !conSupers <- newTVar []
      let
        !console = Object
          { objEntity = conEntity
          , objClass  = ProcDefi
            { procedure'uniq = conClassUniq
            , procedure'name = AttrByName "<console>"
            , procedure'lexi = Just rootScope
            , procedure'decl = ProcDecl { procedure'addr = NamedAttr "<console>"
                                        , procedure'args = PackReceiver []
                                        , procedure'body = Right edhNop
                                        }
            }
          , objSupers = conSupers
          }
        !conScope = objectScope (edh'context pgs) console

      !conArts <- sequence
        [ (AttrByName nm, ) <$> mkHostProc conScope vc nm hp args
        | (vc, nm, hp, args) <-
          [ (EdhMethod, "exit", conExitProc, PackReceiver [])
          , ( EdhMethod
            , "readSource"
            , conReadSourceProc
            , PackReceiver
              [ optionalArg "ps1" $ LitExpr $ StringLiteral defaultEdhPS1
              , optionalArg "ps2" $ LitExpr $ StringLiteral defaultEdhPS2
              ]
            )
          , ( EdhMethod
            , "readCommand"
            , conReadCommandProc
            , PackReceiver
              [ optionalArg "ps1" $ LitExpr $ StringLiteral defaultEdhPS1
              , optionalArg "ps2" $ LitExpr $ StringLiteral defaultEdhPS2
              , optionalArg "inScopeOf" edhNoneExpr
              ]
            )
          , (EdhMethod, "print", conPrintProc, WildReceiver)
          , (EdhMethod, "now"  , conNowProc  , PackReceiver [])
          , ( EdhGnrtor
            , "everyMicros"
            , conEveryMicrosProc
            , PackReceiver [mandatoryArg "interval"]
            )
          , ( EdhGnrtor
            , "everyMillis"
            , conEveryMillisProc
            , PackReceiver [mandatoryArg "interval"]
            )
          , ( EdhGnrtor
            , "everySeconds"
            , conEverySecondsProc
            , PackReceiver [mandatoryArg "interval"]
            )
          ]
        ]
      updateEntityAttrs pgs conEntity conArts

      updateEntityAttrs pgs rootEntity
        $  rootOperators
        ++ rootProcs
        ++ [

            -- console module
             ( AttrByName "console"
             , EdhObject console
             )

            -- math constants
            -- todo figure out proper ways to make these really **constant**,
            --      i.e. not rebindable to other values
           , ( AttrByName "pi"
             , EdhDecimal
               $ Decimal 1 (-40) 31415926535897932384626433832795028841971
             )
           ]

      !scopeSuperMethods <- sequence
        [ (AttrByName nm, )
            <$> mkHostProc (objectScope (edh'context pgs) scopeSuperObj)
                           mc
                           nm
                           hp
                           args
        | (mc, nm, hp, args) <-
          [ (EdhMethod, "__repr__" , scopeReprProc     , PackReceiver [])
          , (EdhMethod, "eval"     , scopeEvalProc     , WildReceiver)
          , (EdhMethod, "get"      , scopeGetProc      , WildReceiver)
          , (EdhMethod, "put"      , scopePutProc      , WildReceiver)
          , (EdhMethod, "attrs"    , scopeAttrsProc    , PackReceiver [])
          , (EdhMethod, "callerLoc", scopeCallerLocProc, PackReceiver [])
          , (EdhMethod, "lexiLoc"  , scopeLexiLocProc  , PackReceiver [])
          , (EdhMethod, "outer"    , scopeOuterProc    , PackReceiver [])
          ]
        ]
      updateEntityAttrs pgs (objEntity scopeSuperObj) scopeSuperMethods

      -- import the parts written in Edh 
      runEdhProc pgs $ importEdhModule' rootEntity
                                        WildReceiver
                                        "batteries/root"
                                        edhEndOfProc

 where
  !rootScope     = worldScope world
  !rootEntity    = objEntity $ thisObject rootScope
  !scopeSuperObj = scopeSuper world

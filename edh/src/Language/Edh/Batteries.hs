
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
import           Data.Text.IO
import qualified Data.HashMap.Strict           as Map

import           System.Console.Haskeline       ( InputT
                                                , outputStrLn
                                                , getInputLine
                                                , handleInterrupt
                                                , withInterrupt
                                                )

import           Data.Lossless.Decimal         as D

import           Language.Edh.Runtime

import           Language.Edh.Batteries.Data
import           Language.Edh.Batteries.Math
import           Language.Edh.Batteries.Assign
import           Language.Edh.Batteries.Reflect
import           Language.Edh.Batteries.Ctrl
import           Language.Edh.Batteries.Runtime
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | The default Edh command prompts
--
-- ps1 is for single line, ps2 for multi-line
-- 
-- note the defaults here are technically in no effect, just advice
-- see implementation of:
--   runtime.readCommands(ps1="Đ: ", ps2="Đ| ")
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | Serialize output to `stdout` from Edh programs, and give them command
-- line input when requested
defaultEdhIOLoop :: EdhRuntime -> InputT IO ()
defaultEdhIOLoop !runtime = liftIO (atomically $ readTQueue ioQ) >>= \case
  ConsoleShutdown    -> return () -- gracefully stop the io loop
  ConsoleOut !txtOut -> do
    outputStrLn $ T.unpack txtOut
    defaultEdhIOLoop runtime
  ConsoleIn !cmdIn !ps1 !ps2 -> do
    liftIO flushLogs
    readInput ps1 ps2 [] >>= \case
      Nothing -> -- reached EOF (end-of-feed) before clean shutdown
        outputStrLn "Your work may have lost, sorry."
      Just !cmd -> do -- got one piece of code
        liftIO $ atomically $ putTMVar cmdIn cmd
        defaultEdhIOLoop runtime
 where
  !ioQ      = consoleIO runtime
  flushLogs = flushRuntimeLogs runtime

  -- | The repl line reader
  readInput :: Text -> Text -> [Text] -> InputT IO (Maybe Text)
  readInput !ps1 !ps2 !initialLines =
    handleInterrupt ( -- start over on Ctrl^C
                     outputStrLn "" >> readLines [])
      $ withInterrupt
      $ readLines initialLines
   where
    readLines pendingLines = getInputLine prompt >>= \case
      Nothing -> case pendingLines of
        [] -> return Nothing
        _ -> -- TODO warn about premature EOF ?
          return Nothing
      Just text ->
        let code = T.pack text
        in  case pendingLines of
              [] -> case T.stripEnd code of
                "{" -> -- an unindented `{` marks start of multi-line input
                  readLines [""]
                _ -> case T.strip code of
                  "" -> -- got an empty line in single-line input mode
                    readLines [] -- start over in single-line input mode
                  _ -> -- got a single line input
                    return $ Just code
              _ -> case T.stripEnd code of
                "}" -> -- an unindented `}` marks end of multi-line input
                  return $ Just $ (T.unlines . reverse) $ init pendingLines
                _ -> -- got a line in multi-line input mode
                  readLines $ code : pendingLines
     where
      prompt :: String
      prompt = case pendingLines of
        [] -> T.unpack ps1
        _  -> T.unpack ps2 <> printf "%2d" (length pendingLines) <> ": "


-- | This runtime serializes all log messages to 'stderr' through a 'TQueue',
-- this is crucial under heavy concurrency.
--
-- known issues:
--  *) can mess up with others writing to 'stderr'
--  *) if all others use 'trace' only, there're minimum messups but emojis 
--     seem to be break points
defaultEdhRuntime :: IO EdhRuntime
defaultEdhRuntime = do
  ioQ         <- newTQueueIO
  envLogLevel <- lookupEnv "EDH_LOG_LEVEL"
  logIdle     <- newEmptyTMVarIO
  logQueue    <- newTQueueIO
  let logLevel = case envLogLevel of
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
        lr <- atomically (tryReadTQueue logQueue) >>= \case
          Just !lr -> do
            void $ atomically $ tryTakeTMVar logIdle
            return lr
          Nothing -> do
            void $ atomically $ tryPutTMVar logIdle ()
            lr <- atomically $ readTQueue logQueue
            void $ atomically $ tryTakeTMVar logIdle
            return lr
        hPutStrLn stderr lr
        logPrinter
      logger :: EdhLogger
      logger !level !srcLoc !pkargs = do
        void $ tryTakeTMVar logIdle
        case pkargs of
          ArgsPack [!argVal] !kwargs | Map.null kwargs ->
            writeTQueue logQueue $! T.pack logPrefix <> logString argVal
          -- todo: format structured log record with log parser in mind
          _ -> writeTQueue logQueue $! T.pack $ logPrefix ++ show pkargs
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
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    finally (unmask logPrinter) $ atomically $ tryPutTMVar logIdle ()
  return EdhRuntime { consoleIO        = ioQ
                    , runtimeLogLevel  = logLevel
                    , runtimeLogger    = logger
                    , flushRuntimeLogs = flushLogs
                    }


installEdhBatteries :: MonadIO m => EdhWorld -> m ()
installEdhBatteries world = liftIO $ do
  rtClassUniq <- newUnique
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do

      -- TODO survey for best practices & advices on precedences here
      --      once it's declared, can not be changed in the world.

      declareEdhOperators
        world
        "<batteries>"
        [ -- format: (symbol, precedence)

        -- the definition operator, creates named value in Edh
          ( ":="
          , 1
          )

        -- the cons operator, creates pairs in Edh
        , ( ":"
          , 2
          ) -- why brittany insists on formatting it like this ?.?

        -- attribute tempter, 
        -- address an attribute off an object if possible, nil otherwise
        , ("?", 9)
        , ( "?$"
          , 9
          )

        -- assignments
        , ( "="
          , 1
          ) -- make it lower than (++), so don't need to quote `a = b ++ c`
        , ("+=", 2)
        , ("-=", 2)
        , ("/=", 2)
        , ( "*="
          , 2
          ) -- why brittany insists on formatting it like this ?.?

        -- arithmetic
        , ("+", 6)
        , ("-", 6)
        , ("*", 7)
        , ("/", 7)
        , ( "**"
          , 8
          )
        -- comparations
        , ( "~="
          , 4
          ) -- deep-value-wise equality test
        , ( "=="
          , 4
          ) -- identity-wise equality test
        , ( "!="
          , 4
          ) -- inversed identity-wise equality test
            -- C style here, as (/=) is used for inplace division
        , (">" , 4)
        , (">=", 4)
        , ("<" , 4)
        , ( "<="
          , 4
          )
          -- logical arithmetic
        , ("&&", 3)
        , ( "||"
          , 3
          ) -- why brittany insists on formatting it like this ?.?

          -- emulate the ternary operator in C:
          --       onCnd ? oneThing : theOther
          --  * Python
          --       onCnd and oneThing or theOther
          --  * Edh
          --       onCnd &> oneThing |> theOther
        , ("&>", 3)
        , ( "|>"
          , 3
          ) -- why brittany insists on formatting it like this ?.?

          -- comprehension
          --  * list comprehension:
          --     [] =< for x from range(100) do x*x
          --  * dict comprehension:
          --     {} =< for x from range(100) do (x, x*x)
          --  * tuple comprehension:
          --     (,) =< for x from range(100) do x*x
        , ( "=<"
          , 1
          ) -- why brittany insists on formatting it like this ?.?
          -- prepand to list
          --     l = [3,7,5]
          --     [2,9] => l
        , ( "=>"
          , 1
          )
          -- element-of test
        , ( "?<="
          , 3
          )

          -- publish to sink
          --     evsPub <- outEvent
        , ( "<-"
          , 1
          )

          -- branch
        , ( "->"
          , 0
          )
          -- catch
        , ( "$=>"
          , -1
          )
          -- finally
        , ( "@=>"
          , -1
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
          [ ("$"  , attrDerefAddrProc)
          , (":=" , defProc)
          , (":"  , consProc)
          , ("?"  , attrTemptProc)
          , ("?$" , attrDerefTemptProc)
          , ("++" , concatProc)
          , ("=<" , cprhProc)
          , ("?<=", elemProc)
          , ("=>" , prpdProc)
          , ("<-" , evtPubProc)
          , ("+"  , addProc)
          , ("-"  , subsProc)
          , ("*"  , mulProc)
          , ("/"  , divProc)
          , ("**" , powProc)
          , ("&&" , logicalAndProc)
          , ("||" , logicalOrProc)
          , ("~=" , valEqProc)
          , ("==" , idEqProc)
          , ("!=" , idNeProc)
          , (">"  , isGtProc)
          , (">=" , isGeProc)
          , ("<"  , isLtProc)
          , ("<=" , isLeProc)
          , ("="  , assignProc)
          , ("->" , branchProc)
          , ("$=>", catchProc)
          , ("@=>", finallyProc)
          , ("<|" , loggingProc)
          ]
        ]

      -- global procedures at world root scope
      !rootProcs <- sequence
        [ (AttrByName nm, ) <$> mkHostProc rootScope mc nm hp args
        | (mc, nm, hp, args) <-
          [ ( EdhMethod
            , "Symbol"
            , symbolCtorProc
            , PackReceiver [RecvArg "description" Nothing Nothing]
            )
          , (EdhMethod, "pkargs"     , pkargsProc     , WildReceiver)
          , (EdhMethod, "repr"       , reprProc       , WildReceiver)
          , (EdhMethod, "dict"       , dictProc       , WildReceiver)
          , (EdhMethod, "null"       , isNullProc     , WildReceiver)
          , (EdhMethod, "type"       , typeProc       , WildReceiver)
          , (EdhMethod, "constructor", ctorProc       , WildReceiver)
          , (EdhMethod, "supers"     , supersProc     , WildReceiver)
          , (EdhMethod, "scope"      , scopeObtainProc, PackReceiver [])
          , ( EdhMethod
            , "makeOp"
            , makeOpProc
            , PackReceiver
              [ RecvArg "lhe"   Nothing Nothing
              , RecvArg "opSym" Nothing Nothing
              , RecvArg "rhe"   Nothing Nothing
              ]
            )
          , (EdhMethod, "makeExpr", makeExprProc, WildReceiver)
          ]
        ]

      !rtEntity <- createHashEntity Map.empty
      !rtSupers <- newTVar []
      let !runtime = Object
            { objEntity = rtEntity
            , objClass  = ProcDefi
                            { procedure'uniq = rtClassUniq
                            , procedure'lexi = Just rootScope
                            , procedure'decl = ProcDecl
                                                 { procedure'name = "<runtime>"
                                                 , procedure'args = PackReceiver
                                                                      []
                                                 , procedure'body = Right edhNop
                                                 }
                            }
            , objSupers = rtSupers
            }
          !rtScope = objectScope (edh'context pgs) runtime

      !rtMethods <- sequence
        [ (AttrByName nm, ) <$> mkHostProc rtScope vc nm hp args
        | (vc, nm, hp, args) <-
          [ (EdhMethod, "exit", rtExitProc, PackReceiver [])
          , ( EdhGnrtor
            , "readCommands"
            , rtReadCommandsProc
            , PackReceiver
              [ RecvArg "ps1" Nothing (Just (LitExpr (StringLiteral "Đ: ")))
              , RecvArg "ps2" Nothing (Just (LitExpr (StringLiteral "Đ| ")))
              ]
            )
          , (EdhMethod, "print", rtPrintProc, WildReceiver)
          , ( EdhGnrtor
            , "everyMicros"
            , rtEveryMicrosProc
            , PackReceiver [RecvArg "interval" Nothing Nothing]
            )
          , ( EdhGnrtor
            , "everyMillis"
            , rtEveryMillisProc
            , PackReceiver [RecvArg "interval" Nothing Nothing]
            )
          , ( EdhGnrtor
            , "everySeconds"
            , rtEverySecondsProc
            , PackReceiver [RecvArg "interval" Nothing Nothing]
            )
          ]
        ]
      updateEntityAttrs pgs rtEntity
        $  [ (AttrByName "debug", EdhDecimal 10)
           , (AttrByName "info" , EdhDecimal 20)
           , (AttrByName "warn" , EdhDecimal 30)
           , (AttrByName "error", EdhDecimal 40)
           , (AttrByName "fatal", EdhDecimal 50)
           ]
        ++ rtMethods

      updateEntityAttrs pgs rootEntity
        $  rootOperators
        ++ rootProcs
        ++ [

            -- runtime module
             ( AttrByName "runtime"
             , EdhObject runtime
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
          [ (EdhMethod, "eval"   , scopeEvalProc   , WildReceiver)
          , (EdhMethod, "get"    , scopeGetProc    , WildReceiver)
          , (EdhMethod, "put"    , scopePutProc    , WildReceiver)
          , (EdhMethod, "attrs"  , scopeAttrsProc  , PackReceiver [])
          , (EdhMethod, "lexiLoc", scopeLexiLocProc, PackReceiver [])
          , (EdhMethod, "outer"  , scopeOuterProc  , PackReceiver [])
          ]
        ]
      updateEntityAttrs pgs (objEntity scopeSuperObj) scopeSuperMethods

      -- import the parts written in Edh 
      runEdhProc pgs
        $ importEdhModule' WildReceiver "batteries/root" edhEndOfProc

 where
  !rootScope     = worldScope world
  !rootEntity    = objEntity $ thisObject rootScope
  !scopeSuperObj = scopeSuper world

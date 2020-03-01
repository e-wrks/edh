
module Language.Edh.Batteries where

import           Prelude

import           System.Environment
import           Text.Read

import           Control.Exception
import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Unique
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Runtime

import           Language.Edh.Batteries.Data
import           Language.Edh.Batteries.Math
import           Language.Edh.Batteries.Assign
import           Language.Edh.Batteries.Reflect
import           Language.Edh.Batteries.Ctrl
import           Language.Edh.Batteries.Runtime


installEdhBatteries :: MonadIO m => EdhWorld -> m ()
installEdhBatteries world = liftIO $ do
  envLogLevel <- lookupEnv "EDH_LOG_LEVEL"
  rtClassUniq <- newUnique
  runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do

      -- TODO survey for best practices & advices on precedences here
      --      once it's declared, can not be changed in the world.

      declareEdhOperators
        world
        "<batteries>"
        [ -- format: (symbol, precedence)

        -- the cons operator, creates pairs in Edh
          ( ":"
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

          -- string coercing concatenation
        , ( "++"
          , 2
          )

          -- logging
        , ("<|", 1)
        ]


      !rootOperators <- mapM
        (\(sym, hp) -> (AttrByName sym, ) <$> mkHostOper world sym hp)
        [ ("$"  , attrDerefAddrProc)
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
        , (">"  , isGtProc)
        , (">=" , isGeProc)
        , ("<"  , isLtProc)
        , ("<=" , isLeProc)
        , ("="  , assignProc)
        , ("->" , branchProc)
        , ("<|" , loggingProc)
        ]

      !rootProcedures <- mapM
        (\(nm, hp) -> (AttrByName nm, ) <$> mkHostProc EdhHostProc nm hp)
        [ ("Symbol"     , symbolCtorProc)
        , ("pkargs"     , pkargsProc)
        , ("dict"       , dictProc)
        , ("null"       , isNullProc)
        , ("type"       , typeProc)
        , ("error"      , errorProc)
        , ("constructor", ctorProc)
        , ("supers"     , supersProc)
        , ("scope"      , scopeObtainProc)
        , ("makeOp"     , makeOpProc)
        , ("makeExpr"   , makeExprProc)
        ]

      !rtEveryMicros  <- mkHostProc EdhHostGenr "everyMicros" rtEveryMicrosProc
      !rtEveryMillis  <- mkHostProc EdhHostGenr "everyMillis" rtEveryMillisProc
      !rtEverySeconds <- mkHostProc EdhHostGenr
                                    "everySeconds"
                                    rtEverySecondsProc
      !rtEntity <- createEntity $ Map.fromList
        [ (AttrByName "debug"       , EdhDecimal 10)
        , (AttrByName "info"        , EdhDecimal 20)
        , (AttrByName "warn"        , EdhDecimal 30)
        , (AttrByName "error"       , EdhDecimal 40)
        , (AttrByName "fatal"       , EdhDecimal 50)
        , (AttrByName "everyMicros" , rtEveryMicros)
        , (AttrByName "everyMillis" , rtEveryMillis)
        , (AttrByName "everySeconds", rtEverySeconds)
        ]
      !rtSupers <- newTVar []
      let !runtime = Object
            { objEntity = rtEntity
            , objClass  = ProcDefi
                            { procedure'lexi = Just $ worldScope world
                            , procedure'decl = ProcDecl
                              { procedure'uniq = rtClassUniq
                              , procedure'name = "<runtime>"
                              , procedure'args = PackReceiver []
                              , procedure'body = StmtSrc
                                                   ( SourcePos
                                                     { sourceName = "<host-code>"
                                                     , sourceLine = mkPos 1
                                                     , sourceColumn = mkPos 1
                                                     }
                                                   , VoidStmt
                                                   )
                              }
                            }
            , objSupers = rtSupers
            }

      gNone    <- mkSymbol "None" True
      gNothing <- mkSymbol "Nothing" True

      installEdhAttrs rootEntity
        $  rootOperators
        ++ rootProcedures
        ++ [
            -- runtime module
             ( AttrByName "runtime"
             , EdhObject runtime
             )

            -- global symbols
           , ( AttrByName "None"
             , -- resembles `None` as in Python
               -- assigning to `nil` in Edh is roughly the same of `delete` as
               -- in JavaScript, and `del` as in Python. Assigning to `None`
               -- will keep the dict entry or object attribute while carries
               -- a semantic of *absence*.
               EdhSymbol gNone
             )
           , ( AttrByName "Nothing"
             , -- Similar to `None`, `Nothing` is idiomatic in VisualBasic
               -- though we don't have `Maybe` monad in Edh, having a `Nothing`
               -- carrying null semantic may be useful in some cases.
               EdhSymbol gNothing
             )

            -- math constants
            -- todo figure out proper ways to make these really **constant**,
            --      i.e. not rebindable to other values
           , ( AttrByName "pi"
             , EdhDecimal
               $ Decimal 1 (-40) 31415926535897932384626433832795028841971
             )
           ]


      !scopeMethods <- mapM
        (\(sym, hp) -> (AttrByName sym, ) <$> mkHostProc EdhHostProc sym hp)
        [ ("eval"   , scopeEvalProc)
        , ("put"    , scopePutProc)
        , ("attrs"  , scopeAttrsProc)
        , ("lexiLoc", scopeLexiLocProc)
        , ("outer"  , scopeOuterProc)
        ]

      installEdhAttrs scopeManiMethods scopeMethods

      case envLogLevel of
        Nothing      -> return ()
        Just "DEBUG" -> setLogLevel 10
        Just "INFO"  -> setLogLevel 20
        Just "WARN"  -> setLogLevel 30
        Just "ERROR" -> setLogLevel 40
        Just "FATAL" -> setLogLevel 50
        Just ns      -> case readEither ns of
          Left  _           -> return ()
          Right (ln :: Int) -> setLogLevel ln


      -- import the parts written in Edh 
      runEdhProg pgs $ importEdhModule' WildReceiver "batteries/root" edhNop

 where
  !rootEntity = objEntity $ thisObject $ worldScope world
  scopeManiMethods :: Entity
  !scopeManiMethods = objEntity $ scopeSuper world
  !wrt              = worldRuntime world
  setLogLevel :: LogLevel -> STM ()
  setLogLevel l = do
    rt <- takeTMVar wrt
    catchSTM (putTMVar wrt rt { runtimeLogLevel = l })
      $ \(e :: SomeException) -> tryPutTMVar wrt rt >> throwSTM e

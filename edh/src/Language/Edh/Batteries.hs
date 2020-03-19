
module Language.Edh.Batteries where

import           Prelude

import           System.Environment
import           Text.Read

import           Control.Exception
import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Unique
import qualified Data.HashMap.Strict           as Map

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

          -- string coercing concatenation
        , ( "++"
          , 2
          )

          -- logging
        , ("<|", 1)
        ]

      -- global operators at world root scope
      !rootOperators <- sequence
        [ (AttrByName sym, ) <$> mkHostOper world rootScope sym hp
        | (sym, hp) <-
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
          , (EdhMethod, "dict"       , dictProc       , WildReceiver)
          , (EdhMethod, "null"       , isNullProc     , WildReceiver)
          , (EdhMethod, "type"       , typeProc       , WildReceiver)
          , (EdhMethod, "error"      , errorProc      , WildReceiver)
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
                            , procedure'lexi = Just $ rootScope
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
      !rtGenrs <- sequence
        [ (AttrByName nm, ) <$> mkHostProc
            rtScope
            EdhGenrDef
            nm
            hp
            (PackReceiver [RecvArg "interval" Nothing Nothing])
        | (nm, hp) <-
          [ ("everyMicros" , rtEveryMicrosProc)
          , ("everyMillis" , rtEveryMillisProc)
          , ("everySeconds", rtEverySecondsProc)
          ]
        ]
      updateEntityAttrs pgs rtEntity
        $  [ (AttrByName "debug", EdhDecimal 10)
           , (AttrByName "info" , EdhDecimal 20)
           , (AttrByName "warn" , EdhDecimal 30)
           , (AttrByName "error", EdhDecimal 40)
           , (AttrByName "fatal", EdhDecimal 50)
           ]
        ++ rtGenrs

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
      runEdhProg pgs
        $ importEdhModule' WildReceiver "batteries/root" edhEndOfProc

 where
  !rootScope     = worldScope world
  !rootEntity    = objEntity $ thisObject rootScope
  !scopeSuperObj = scopeSuper world
  !wrt           = worldRuntime world
  setLogLevel :: LogLevel -> STM ()
  setLogLevel l = do
    rt <- takeTMVar wrt
    catchSTM (putTMVar wrt rt { runtimeLogLevel = l })
      $ \(e :: SomeException) -> tryPutTMVar wrt rt >> throwSTM e

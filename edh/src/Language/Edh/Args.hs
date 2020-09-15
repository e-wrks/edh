{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Args
  ( NamedArg(..)
  , type (!:)
  , type (?:)
  , pattern Arg
  , arg
  , optionalArg
  , defaultArg
  )
where


import           Prelude

import           GHC.TypeLits                   ( Symbol )
import           Data.Kind                      ( Type )
import           Data.Maybe


newtype NamedArg (t :: Type) (name :: Symbol) = NamedArg t
type name !: t = NamedArg t name
type name ?: t = NamedArg (Maybe t) name

pattern Arg :: t -> name !: t
pattern Arg t = NamedArg t
{-# COMPLETE Arg #-}

arg ::  name !: t -> t 
arg (NamedArg a) = a

optionalArg :: name ?: t -> Maybe t
optionalArg (NamedArg !ma) = ma

defaultArg :: t -> name ?: t -> t
defaultArg !a (NamedArg !ma) = fromMaybe a ma


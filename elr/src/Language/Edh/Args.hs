{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Args
  ( NamedEdhArg(..) -- todo find a way to hide this from EHI
  , type (!:)
  , type (?:)
  , pattern EdhArg
  , mandatoryArg
  , optionalArg
  , defaultArg
  )
where


import           Prelude

import           GHC.TypeLits                   ( Symbol )
import           Data.Kind                      ( Type )
import           Data.Maybe


newtype NamedEdhArg (t :: Type) (name :: Symbol) = NamedEdhArg t
type name !: t = NamedEdhArg t name
type name ?: t = NamedEdhArg (Maybe t) name

pattern EdhArg :: t -> name !: t
pattern EdhArg t = NamedEdhArg t
{-# COMPLETE EdhArg #-}

mandatoryArg ::  name !: t -> t 
mandatoryArg (NamedEdhArg a) = a

optionalArg :: name ?: t -> Maybe t
optionalArg (NamedEdhArg !ma) = ma

defaultArg :: t -> name ?: t -> t
defaultArg !a (NamedEdhArg !ma) = fromMaybe a ma


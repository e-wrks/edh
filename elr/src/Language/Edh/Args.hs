{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Args
  ( NamedEdhArg (..), -- todo find a way to hide this from EHI
    type (!:),
    type (?:),
    pattern EdhArg,
    mandatoryArg,
    optionalArg,
    defaultArg,
    QtyAsIn (..),
    ComputArg (..),
    Effective (..),
    computArgName,
    type (@:),
    type ($:),
    appliedArg,
    effectfulArg,
    Being (..),
  )
where

import Data.Kind (Constraint, Type)
import Data.Lossless.Decimal (Decimal)
import Data.Maybe
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Prelude

-- * Monadic Edh Procedure Arguments

newtype NamedEdhArg (t :: Type) (name :: Symbol) = NamedEdhArg t

type name !: t = NamedEdhArg t name

type name ?: t = NamedEdhArg (Maybe t) name

pattern EdhArg :: t -> name !: t
pattern EdhArg t = NamedEdhArg t

{-# COMPLETE EdhArg #-}

mandatoryArg :: name !: t -> t
mandatoryArg (NamedEdhArg a) = a

optionalArg :: name ?: t -> Maybe t
optionalArg (NamedEdhArg !ma) = ma

defaultArg :: t -> name ?: t -> t
defaultArg !a (NamedEdhArg !ma) = fromMaybe a ma

newtype QtyAsIn (uom :: Symbol) = Qty Decimal

-- * Curried & Effected Edh Procedure Arguments

newtype ComputArg (a :: Type) (name :: Symbol) = ComputArg a

computArgName :: forall (name :: Symbol). KnownSymbol name => Text
computArgName = T.pack $ symbolVal (Proxy :: Proxy name)

newtype Effective a = Effective a

type name @: a = ComputArg a name

type name $: a = ComputArg (Effective a) name

appliedArg :: name @: a -> a
appliedArg (ComputArg a) = a

effectfulArg :: name $: a -> a
effectfulArg (ComputArg (Effective a)) = a

-- * Higher Kinded Argument Type Helpers

data Being (k :: * -> Constraint) where
  Being :: forall k t. (k t) => t -> Being k

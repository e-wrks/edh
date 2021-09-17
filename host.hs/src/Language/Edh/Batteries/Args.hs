module Language.Edh.Batteries.Args
  ( ComputArg (..),
    Effective (..),
    computArgName,
    type (@:),
    type ($:),
    appliedArg,
    effectfulArg,
  )
where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Prelude

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

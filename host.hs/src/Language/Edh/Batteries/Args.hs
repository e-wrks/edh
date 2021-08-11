module Language.Edh.Batteries.Args
  ( ScriptArg (..),
    Effective (..),
    scriptArgName,
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

newtype ScriptArg (a :: Type) (name :: Symbol) = ScriptArg a

scriptArgName :: forall (name :: Symbol). KnownSymbol name => Text
scriptArgName = T.pack $ symbolVal (Proxy :: Proxy name)

newtype Effective a = Effective a

type name @: a = ScriptArg a name

type name $: a = ScriptArg (Effective a) name

appliedArg :: name @: a -> a
appliedArg (ScriptArg a) = a

effectfulArg :: name $: a -> a
effectfulArg (ScriptArg (Effective a)) = a

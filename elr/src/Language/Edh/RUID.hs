-- | Runtime wide Unique IDentifier
module Language.Edh.RUID
  ( RUID, -- the constructor / pattern is considered an implementation detail
    newRUID,
    newRUID'STM,
  )
where

import Control.Concurrent.STM
import Data.Hashable
import Data.IORef
import GHC.Conc (unsafeIOToSTM)
import System.IO.Unsafe (unsafePerformIO)
import Prelude

-- | Currently implemented as an 'Integer' counter
newtype RUID = RUID Integer
  deriving (Eq, Hashable, Ord)

instance Show RUID where
  show (RUID cnt) = "#" <> show cnt <> "#"

-- | Assign a new identifier
newRUID :: IO RUID
newRUID = atomicModifyIORef' cntrRUID $ \cnt -> (cnt + 1, RUID cnt)

-- | Assign a new identifier
--
-- 'STM' retry will waste some identifier values, but considered okay.
newRUID'STM :: STM RUID
newRUID'STM = unsafeIOToSTM newRUID

-- | The "global" (but only runtime wide) counter for unique identifiers
cntrRUID :: IORef Integer
cntrRUID = unsafePerformIO $ newIORef 101
{-# NOINLINE cntrRUID #-}

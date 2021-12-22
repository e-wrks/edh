-- | Edh Host Interface
--
-- With Haskell as the host language, Edh as the surface language,
-- this defines the interface for host code in Haskell to create &
-- control embedded Edh worlds, so as to splice host codebases
-- (featuring immutability, purity, and fast-in-machine-speed)
-- wrapped as various host procedures.
module Language.Edh.EHI
  ( D.Decimal (..),
    module Language.Edh.Args,
    module Language.Edh.Monad,
    module Language.Edh.Comput,
    module Language.Edh.RtTypes,
    module Language.Edh.IOPD,
    module Language.Edh.RUID,
    module Language.Edh.Control,
    module Language.Edh.CoreLang,
    module Language.Edh.InterOpM,
    module Language.Edh.Batteries,
    module Language.Edh.RuntimeM,

    -- ** Edh Runtime error
    getEdhErrCtx,
    edhCreateError,
    throwHostSTM,
    throwHostSTM',
    throwHostIO,
    throwHostIO',

    -- ** IO/CPS channel api
    newBChanIO,
    closeBChanIO,
    readBChan,
    writeBChan,

    -- ** Re-exports
    Hashable (..),
  )
where

import Data.Hashable
import qualified Data.Lossless.Decimal as D
import Language.Edh.Args
import Language.Edh.Batteries
import Language.Edh.Comput
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.InterOpM
import Language.Edh.Monad
import Language.Edh.RUID
import Language.Edh.RtTypes
import Language.Edh.RuntimeM

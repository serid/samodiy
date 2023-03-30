module RuntimeException where

import Control.Exception (Exception)
import Data.Typeable (Typeable)

newtype RuntimeException = RuntimeException { unRuntimeException :: String } deriving (Show, Typeable)

-- instance Show RuntimeException where
--     show = unRuntimeException

instance Exception RuntimeException where
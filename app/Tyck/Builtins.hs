{-# LANGUAGE DeriveGeneric #-}

module Tyck.Builtins where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Util.ShowText (ShowText (..))

data Builtin =
    IntType
    | BInt !Int
    | IntAdd
    deriving (Eq, Generic)

instance NFData Builtin

instance ShowText Builtin where
    showText IntType = "Int"
    showText (BInt n) = showText n
    showText IntAdd = "IntAdd"
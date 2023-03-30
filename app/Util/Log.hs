{-# LANGUAGE TypeFamilies #-}

module Util.Log (Log, addLog, addLogLn, runLog) where

import Effectful (Effect, DispatchOf, Dispatch(Static), Eff, type (:>), IOE, liftIO)
import Effectful.Dispatch.Static (StaticRep, SideEffects(WithSideEffects), getStaticRep, unsafeEff_, evalStaticRep, unsafeLiftMapIO)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Util.Util (TextChain)
import Data.Text (Text)
import Control.Exception (SomeException, try, evaluate)
import Control.Monad ((>=>))
import Control.DeepSeq (force, NFData)

data Log :: Effect

type instance DispatchOf Log = 'Static 'WithSideEffects
newtype instance StaticRep Log = Log (IORef TextChain)

addLog :: Log :> es => Text -> Eff es ()
addLog str = do
    Log storage <- getStaticRep
    _ <- unsafeEff_ $ evaluate str
    unsafeEff_ $ modifyIORef' storage (<> [str])

addLogLn :: Log :> es => Text -> Eff es ()
addLogLn = addLog >=> const (addLog "\n")

runLog :: (IOE :> es, NFData a) => Eff (Log ': es) a -> Eff es (TextChain, Either SomeException a)
runLog ef = do
    logs <- liftIO $ newIORef []
    let computation = evalStaticRep (Log logs) ef
    -- SAFETY: lemme just catch exceptions with no care in the world
    --result <- liftIO $ try $ runEff computation
    let trial comp = try do
            value <- comp
            evaluate $ force value -- Uncover any lazy exceptions
    result <- unsafeLiftMapIO trial computation
    finalLogs <- liftIO $ readIORef logs
    pure (finalLogs, result)
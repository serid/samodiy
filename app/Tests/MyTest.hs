module Tests.MyTest where

import Prelude hiding (putStrLn)

import Tyck.Model (NamefulExpr, Expr)
import Util.Util (TextChain, textChainToText, fmt, execError)
import Tyck.Mod (InferenceResult (..), runInference, check1, infer1, InferenceResultNoIce (..), rethrowIce, eraseNames)
import Effectful (Eff, IOE, MonadIO (liftIO), runEff, raise)
import Util.Log (Log, addLogLn, runLog)
import Data.Text (append, Text, unpack)
import qualified Data.Text as T
import Control.Exception (throwIO)
import RuntimeException (RuntimeException(..))
import Util.ShowText (ShowText(..))
import Data.Text.IO (putStrLn)
import Control.DeepSeq (NFData)
import Test.HUnit (assertEqual)

inferTestWithExpected :: NamefulExpr -> NamefulExpr -> MyTest ()
inferTestWithExpected expr namefulTy1 = do
    ty1 <- liftIO $ execError $ eraseNames namefulTy1
    ty2 <- noDiagnosticTest =<< inferTest expr
    addLogLn $ fmt "Inferred type\n  %\nFor\n  %" [showText ty2, showText expr]
    liftIO $ assertEqual "" ty1 ty2

inferTest :: NamefulExpr -> MyTest (InferenceResultNoIce Expr)
inferTest namefulExpr = do
    expr <- liftIO $ execError $ eraseNames namefulExpr
    result <- raise $ runInference $ infer1 expr
    printLogsAndRethrowIce result

checkTest :: NamefulExpr -> NamefulExpr -> MyTest (InferenceResultNoIce ())
checkTest namefulExpr namefulTy = do
    expr <- liftIO $ execError $ eraseNames namefulExpr
    ty <- liftIO $ execError $ eraseNames namefulTy
    addLogLn $ fmt "Checking\n  %\nAgainst\n  %" [showText expr, showText ty]
    result <- raise $ runInference $ check1 expr ty
    printLogsAndRethrowIce result

noDiagnosticTest :: InferenceResultNoIce a -> MyTest a
noDiagnosticTest result = do
    case result of
        Ok x -> pure x
        Diagnostic diagnostic -> do
            addLogLn "Diagnostic:"
            addLogLn diagnostic
            liftIO (throwIO (RuntimeException "found a diagnostic"))

diagnosticTest :: Text -> InferenceResultNoIce () -> MyTest ()
diagnosticTest expectedDiagnostic result = do
    case result of
        Ok _ -> liftIO $ throwIO (userError $ unpack $ "expected a diagnostic: " `append` expectedDiagnostic)
        Diagnostic diagnostic -> liftIO $ assertEqual "" expectedDiagnostic (extractMainMessageDroppingTheCallStack diagnostic)
    where
        extractMainMessageDroppingTheCallStack = head . T.splitOn " at\n"

printLogsAndRethrowIce :: (TextChain, InferenceResult a) -> MyTest (InferenceResultNoIce a)
printLogsAndRethrowIce (logs, result) = do
    addLogLn "MyTest logs:"
    addLogLn $ textChainToText logs
    rethrowIce result

type MyTest a = Eff (Log ': IOE ': '[]) a

runMyTest :: NFData a => MyTest a -> IO a
runMyTest test = do
    (logs, result) <- runEff $ runLog test
    case result of
        -- Only print logs in case of an error
        Left except -> do
            putStrLn $ textChainToText (if null logs then ["empty logs"] else logs)
            throwIO except
        Right x -> pure x
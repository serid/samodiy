module Main where

import Data.Text.IO (putStrLn)
import Tyck.Model (GExpr (..), apply, lam, var, GStmtF (LetF), do_, builtin, forall)
import Util.Util (constO, execError)
import Prelude hiding (putStrLn)
import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.API (Test)
import Test.HUnit (assertEqual)
import Tyck.Reductor (whnf)
import Effectful (liftIO)
import Util.Log (addLogLn)
import Tests.MyTest (MyTest, checkTest, runMyTest, noDiagnosticTest, diagnosticTest, inferTestWithExpected)
import Util.Free (execParser, intP)
import Compiler.Syntax (classP, ClassDef (ClassDef), tokenize, classP1, MethodDef (MethodDef))
import Tyck.Builtins (Builtin(..))

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"
    -- defaultMainWithOpts tests (mempty { ropt_color_mode = Just ColorAlways })
    defaultMain tests

tests :: [Test]
tests = [
        testGroup "reductions" [
            testCase "reduction 1" $ runMyTest test1,
            testCase "reduction in forall" $ runMyTest testSubstitutionInsideForall,
            testCase "reduction do" $ runMyTest testDo,
            testCase "reduction do 2" $ runMyTest testDo2,
            testCase "reduction do 3" $ runMyTest testDo3
        ],
        testGroup "typechecks" [
            testCase "typecheck lambda forall" $ runMyTest test2,
            testCase "typecheck application" $ runMyTest test3,
            testCase "typecheck application diagnostic" $ runMyTest test4,
            testCase "typecheck application inference" $ runMyTest test5
        ],
        testGroup "parses" [
            testCase "parse int" $ runMyTest test6,
            testCase "parse char class" $ runMyTest test7,
            testCase "parse class" $ runMyTest test8
        ]
    ]

test1 :: MyTest ()
test1 = do
    let result = whnf $ apply (lam [builtin IntType, builtin IntType] (var 0)) [builtin $ BInt 42, builtin $ BInt 127]
    actual <- liftIO $ execError result
    liftIO $ assertEqual "" (builtin $ BInt 127) actual

testSubstitutionInsideForall :: MyTest ()
testSubstitutionInsideForall = do
    let result = whnf $ apply (lam [builtin IntType] $ forall [var 20, var 30] (var 2)) [var 10]
    actual <- liftIO $ execError result
    liftIO $ assertEqual "" (forall [var 19, var 29] (var 12)) actual

testDo :: MyTest ()
testDo = do
    let result = whnf $ do_ [LetF () $ builtin (BInt 10), LetF () $ builtin (BInt 20)] $ apply (builtin IntAdd) [var 0, var 1]
    actual <- liftIO $ execError result
    liftIO $ assertEqual "" (builtin (BInt 30)) actual

testDo2 :: MyTest ()
testDo2 = do
    let result = whnf $ do_ [LetF () $ builtin (BInt 25), LetF () $ var 0] $ apply (builtin IntAdd) [var 0, var 1]
    actual <- liftIO $ execError result
    liftIO $ assertEqual "" (builtin (BInt 50)) actual

testDo3 :: MyTest ()
testDo3 = do
    let result = whnf $ apply (lam [builtin IntType] $ do_ [LetF () $ builtin (BInt 25), LetF () $ apply (builtin IntAdd) [builtin (BInt 1), var 1]] $ var 0) [builtin (BInt 5)]
    actual <- liftIO $ execError result
    liftIO $ assertEqual "" (builtin (BInt 6)) actual

test2 :: MyTest ()
test2 = do
    let expr = Lam constO [("x", Builtin constO IntType), ("x", Builtin constO IntType)] (Builtin constO $ BInt 10)
    let ty = Forall constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Builtin constO IntType)
    inferTestWithExpected expr ty

    addLogLn ""

    let expr2 = Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y")
    let ty2 = Forall constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Builtin constO IntType)
    checkTest expr2 ty2 >>= noDiagnosticTest

test3 :: MyTest ()
test3 = do
    let expr = Apply constO
            (Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y"))
            [Builtin constO $ BInt 10, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    checkTest expr ty >>= noDiagnosticTest

test4 :: MyTest ()
test4 = do
    let expr = Apply constO
            (Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y"))
            [Sort constO, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    checkTest expr ty >>= diagnosticTest "unification error: Sort and Int\ntheir whnf: Sort and Int"

test5 :: MyTest ()
test5 = do
    let expr = Apply constO
            (Lam constO [("x", Hole constO), ("y", Hole constO)] (Var constO "y"))
            [Builtin constO $ BInt 10, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    inferTestWithExpected expr ty

test6 :: MyTest ()
test6 = do
    liftIO $ assertEqual "" (Right 123) (execParser intP "123")

test7 :: MyTest ()
test7 = do
    let src = "class Doge end"
    liftIO $ assertEqual "" (Right $ ClassDef "Doge" []) (execParser classP1 src)

test8 :: MyTest ()
test8 = do
    let src = "class Doge\n\
        \fun print()\n\
        \end\n\
        \end"
    let expected = ClassDef "Doge" [MethodDef "print" [] []]
    liftIO $ assertEqual "" (Right expected) (execParser classP =<< tokenize src)
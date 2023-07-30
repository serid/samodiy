{-# LANGUAGE QuasiQuotes #-}
module Main where

import Data.Text.IO (putStrLn)
import Tyck.Model (GExpr (..), apply, lam, var, GStmtF (LetF), do_, builtin, forall)
import Util.Util (constO)
import Prelude hiding (putStrLn)
import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.API (Test)
import Test.HUnit (assertEqual)
import Tyck.Reductor (whnf)
import Effectful (liftIO, inject)
import Util.Log (addLogLn)
import Tests.MyTest (MyTest, checkTest, runMyTest, noDiagnosticTest, diagnosticTest, inferTestWithExpected, reductionTest)
import Util.Free (execParser, intP)
import Compiler.Syntax (ClassDef (ClassDef), classP1, moduleP, ModuleDef (..), ToplevelDef (ToplevelClass, ToplevelLet), execSP)
import Tyck.Builtins (Builtin(..))
import NeatInterpolation (trimming)
import Data.Text (unpack)

main :: IO ()
main = do
    putStrLn "Hello, Haskell!"
    -- defaultMainWithOpts tests (mempty { ropt_color_mode = Just ColorAlways })
    defaultMain tests

tests :: [Test]
tests = [
        testGroup "reductions" [
            testCase "reduction K" $ runMyTest testReductionK,
            testCase "reduction in forall" $ runMyTest testSubstitutionInsideForall,
            testCase "reduction do" $ runMyTest testDo,
            testCase "reduction do 2" $ runMyTest testDo2,
            testCase "reduction do 3" $ runMyTest testDo3
        ],
        testGroup "typechecks" [
            testCase "typecheck lambda forall" $ runMyTest testLambdaForall,
            testCase "typecheck application" $ runMyTest testApplication,
            testCase "typecheck application diagnostic" $ runMyTest testApplicationDiagnostic,
            testCase "typecheck application inference" $ runMyTest testApplicationDiagnosticInference
        ],
        testGroup "parses" [
            testCase "tokenize int" $ runMyTest testTokenizeInt,
            testCase "parse class scannerless" $ runMyTest testParseClass,
            testCase "parse module" $ runMyTest moduleParserTest
        ]
    ]

testReductionK :: MyTest ()
testReductionK = do
    reductionTest "do fun(a, b) b end (42, 127)" "127"

testSubstitutionInsideForall :: MyTest ()
testSubstitutionInsideForall = do
    let result = whnf $ apply (lam [builtin IntType] $ forall [var 20, var 30] (var 2)) [var 10]
    actual <- inject result
    liftIO $ assertEqual "" (forall [var 19, var 29] (var 12)) actual

testDo :: MyTest ()
testDo = do
    let result = whnf $ do_ [LetF () $ builtin (BInt 10), LetF () $ builtin (BInt 20)] $ apply (builtin IntAdd) [var 0, var 1]
    actual <- inject result
    liftIO $ assertEqual "" (builtin (BInt 30)) actual

testDo2 :: MyTest ()
testDo2 = do
    let result = whnf $ do_ [LetF () $ builtin (BInt 25), LetF () $ var 0] $ apply (builtin IntAdd) [var 0, var 1]
    actual <- inject result
    liftIO $ assertEqual "" (builtin (BInt 50)) actual

testDo3 :: MyTest ()
testDo3 = do
    let result = whnf $ apply (lam [builtin IntType] $ do_ [LetF () $ builtin (BInt 25), LetF () $ apply (builtin IntAdd) [builtin (BInt 1), var 1]] $ var 0) [builtin (BInt 5)]
    actual <- inject result
    liftIO $ assertEqual "" (builtin (BInt 6)) actual

testLambdaForall :: MyTest ()
testLambdaForall = do
    let expr = Lam constO [("x", Builtin constO IntType), ("x", Builtin constO IntType)] (Builtin constO $ BInt 10)
    let ty = Forall constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Builtin constO IntType)
    inferTestWithExpected expr ty

    addLogLn ""

    let expr2 = Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y")
    let ty2 = Forall constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Builtin constO IntType)
    checkTest expr2 ty2 >>= noDiagnosticTest

testApplication :: MyTest ()
testApplication = do
    let expr = Apply constO
            (Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y"))
            [Builtin constO $ BInt 10, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    checkTest expr ty >>= noDiagnosticTest

testApplicationDiagnostic :: MyTest ()
testApplicationDiagnostic = do
    let expr = Apply constO
            (Lam constO [("x", Builtin constO IntType), ("y", Builtin constO IntType)] (Var constO "y"))
            [Sort constO, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    checkTest expr ty >>= diagnosticTest "unification error: Sort and Int\ntheir whnf: Sort and Int"

testApplicationDiagnosticInference :: MyTest ()
testApplicationDiagnosticInference = do
    let expr = Apply constO
            (Lam constO [("x", Hole constO), ("y", Hole constO)] (Var constO "y"))
            [Builtin constO $ BInt 10, Builtin constO $ BInt 20]
    let ty = Builtin constO IntType
    inferTestWithExpected expr ty

testTokenizeInt :: MyTest ()
testTokenizeInt = do
    liftIO $ assertEqual "" (Right 123) (execParser intP "123")

testParseClass :: MyTest ()
testParseClass = do
    let src = "class Doge end"
    liftIO $ assertEqual "" (Right $ ClassDef "Doge" []) (execParser classP1 src)

-- test8 :: MyTest ()
-- test8 = do
--     let src = "class Doge\n\
--         \end\n\
--         \fun print()\n\
--         \end"
--     let expected = ModuleDef [ToplevelClass $ ClassDef "Doge" [],
--             Toplevel $ FunDef "print" [] []]
--     liftIO $ assertEqual "" (Right expected) (execParser moduleP =<< tokenize src)

moduleParserTest :: MyTest ()
moduleParserTest = do
    let src = unpack [trimming|
        class Doge
        end
        let print = fun() =>
            10
        end
    |]
    let expected = ModuleDef [ToplevelClass $ ClassDef "Doge" [],
            ToplevelLet "print" (Hole constO) (Lam constO [] $ Builtin constO (BInt 10))]
    liftIO $ assertEqual "" (Right expected) (execSP moduleP src)
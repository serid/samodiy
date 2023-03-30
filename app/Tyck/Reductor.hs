-- Implementation of a lambda calculus interpreter using de bruijn indices as described in
-- https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture14.pdf

-- {-# LANGUAGE TemplateHaskell #-}

module Tyck.Reductor (whnf) where

import Control.Lens ((%~))
import Data.Functor.Foldable ( Corecursive(embed), para )
import Data.Text (Text)
import Effectful (runPureEff, Eff)
import Tyck.Model (Expr, GExpr (..), GExprF (..), prismExprLF, forCountingMLF, var, CompilerStage (Debruijn), GStmtF (..), forCountingMDo)
import Util.Util (fmt, throwText, checkEqual, constO, unreachable, unreachableError)
import Util.ShowText (showText)
import Data.Foldable (foldl')
import Effectful.Error.Static (Error)
import Safe.Exact (zipExact)
import Tyck.Builtins (Builtin(..))

whnf :: Expr -> Eff (Error Text ': es) Expr
whnf arg@(Hole _) = pure arg
whnf arg@(Sort _) = pure arg
whnf (Var _ _) = throwText "unexpected"
whnf arg@(ExVar _ _) = pure arg -- Assumes that all existentials are already substituted
whnf arg@(Lam {}) = pure arg
whnf arg@(Forall {}) = pure arg
whnf (Apply _ fun args) = do
    nfFun <- whnf fun
    case nfFun of
        Lam _ binds body -> do
            n <- checkEqual (length binds) (length args) $ fmt "expected % arguments, but found %" [showText $ length binds, showText $ length args]
            let zippedArgs = zipExact (shift n 0 <$> args) (fromIntegral <$> reverse [0..n - 1])
            let folder body1 (arg, index) = replace arg index body1
            let replacer = foldl' folder body
            whnf $ shift (-n) 0 $ replacer zippedArgs
        Builtin _ b -> reduceBuiltinApplication b args
        _ -> throwText "type error"
-- If all arguments are builtins, call a builtin handler
-- whnf (Apply _ (Builtin _ b) (fmap (^? exprBuiltin) >>> sequenceA -> Just args)) = pure $ reduceBuiltinApplication b args
whnf arg@(Do {}) = whnf =<< go arg
    where
        go :: Expr -> Eff (Error Text ': es) Expr
        go (Do _ [] final1) = pure final1
        -- go [x] = x ^? _StmtExprF & maybeToEff (throwText "last stmt should be an expression")
        go (Do _ (x : xs) final1) = do
                case x of
                    LetF () ini -> do
                        -- todo: add IO effect and stop reducing when not needed
                        -- normalized <- whnf ini
                        -- normalizedTail <- go xs
                        -- whnf $ shiftAndReplace 0 normalized normalizedTail
                        go $ shiftAndReplace 0 ini (Do constO xs final1)
                    StmtExprF expr -> do
                        -- _ <- whnf expr
                        go (Do constO xs final1)
        go _ = unreachable
whnf arg@(Builtin _ _) = pure arg

reduceBuiltinApplication :: Builtin -> [Expr] -> Eff (Error Text ': es) Expr
reduceBuiltinApplication b args = do
    nfArgs <- traverse whnf args
    case (b, nfArgs) of
        (IntAdd, [Builtin _ (BInt x), Builtin _ (BInt y)]) -> pure $ Builtin constO $ BInt $ x + y
        _ -> unreachableError

-- todo:
-- 1. DONE fix whnf (replace let variables in following let initializers)
-- 2. DONE fix functions replace and shift to account for do blocks
-- 3. fix type inference inside do blocks -- algorithms should add the binder to context after each let statement

shiftAndReplace :: Word -> Expr -> Expr -> Expr
shiftAndReplace index arg body = shift (-1) 0 (replace (shift 1 0 arg) index body)

shift :: Int -> Word -> Expr -> Expr
shift i c = para go
    where
        go :: GExprF 'Debruijn (Expr, Expr) -> Expr
        go (VarF _ n) = var $ if n < c then n else fromIntegral $ fromIntegral n + i
        go arg@(LamF {}) = shiftLF (embed $ fmap fst arg)
        go arg@(ForallF {}) = shiftLF (embed $ fmap fst arg)
        go arg@(DoF {}) =
            runPureEff $ forCountingMDo c (\cutoff stmt -> pure $ case stmt of
                LetF () ini -> LetF () $ shift i cutoff ini
                StmtExprF e -> StmtExprF (shift i cutoff e))
                (\cutoff final -> pure $ shift i cutoff final) (fmap fst arg)
        -- In other cases just pass the folded results
        go arg = embed $ fmap snd arg

        shiftLF :: Expr -> Expr
        shiftLF = prismExprLF %~ (runPureEff . forCountingMLF c (\cutoff expr1 ->
            pure $ shift i cutoff expr1))

replace :: Expr -> Word -> Expr -> Expr
replace substitute m = para go
    where
        go :: GExprF 'Debruijn (Expr, Expr) -> Expr
        go arg@(VarF _ n) = if n == m then substitute else embed $ fmap snd arg
        go arg@(LamF {}) = replaceLF (embed $ fmap fst arg)
        go arg@(ForallF {}) = replaceLF (embed $ fmap fst arg)
        go arg@(DoF {}) =
            runPureEff $ forCountingMDo 0 (\depth stmt -> pure $ case stmt of
                LetF () ini -> LetF () $ replace (shift (fromIntegral depth) 0 substitute) (m + depth) ini
                StmtExprF e -> StmtExprF $ replace (shift (fromIntegral depth) 0 substitute) (m + depth) e)
                (\depth final -> pure $ replace (shift (fromIntegral depth) 0 substitute) (m + depth) final) (fmap fst arg)
        -- In other cases just pass the folded results
        go arg = embed $ fmap snd arg

        replaceLF :: Expr -> Expr
        -- bugged code:
        -- replaceLF = prismExprLF %~ (runPureEff . forCountingMLF m (\index expr1 ->
        --     pure $ replace (shift 1 0 substitute) index expr1))
        replaceLF = prismExprLF %~ (runPureEff . forCountingMLF 0 (\depth expr1 ->
            pure $ replace (shift (fromIntegral depth) 0 substitute) (m + depth) expr1))
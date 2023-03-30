-- A type inference algorithm for dependent types
-- Loosely based on https://www.cl.cam.ac.uk/~nk480/bidir.pdf.
-- I don't use subtyping and my language is dependently typed so
-- only basic structure remains of the algorthm presented in the article.
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE TupleSections #-}

module Tyck.Mod (infer1, check1, runInference, eraseNames, rethrowIce, InferenceResult (..), InferenceResultNoIce (..)) where

import Control.Lens ((<&>), (^?!), (^.), (%~), toListOf, traverseOf_, (^?), traverseOf)
import Data.Foldable (traverse_, forM_)
import Data.Text (Text)
import Effectful (Eff, IOE, inject, type (:>), liftIO, raise)
import Effectful.Error.Static (Error, runError)
import Effectful.State.Static.Local (evalState, get, modify, modifyM)
import Util.ShowText (ShowText (showText))
import Tyck.Model (ContextEntry (..), Expr, GExpr (..), TyckState (TyckState), annot, context, sort, prismExprLF, GLamForall (GLamForall), LFTag (..), traversalExprExprs, ctxVarIx, isVar, getEntryByIx, InferenceE, GExprF (..), derefExistential, ctxExId, ctxExType, whereExId, whereVarIx, getOneEntry, unpadExprs, padExprs, derefExistentialToId, NamefulExpr, CompilerStage (..), gExprTraverse, Stmt, GStmtF (StmtExprF, LetF), builtin, forall, LamForall, toLamForall, fromLamForall)
import Util.Util (fmt, joinToString, throwText, TextChain, constO, showCallStack, unreachableError, fromTrue, mapLeft, wordFindIndex, fromJustText, weakenReader)
import Util.Log (Log, runLog, addLog, addLogLn)
import Control.Exception (SomeException, throwIO)
import Tyck.Reductor (whnf)
import Control.Arrow (second, (>>>))
import Data.Functor.Foldable (cata, embed)
import Data.Functor.Base (ListF(..))
import Data.Functor (($>), void)
import Safe.Foldable (maximumMay)
import Control.DeepSeq (NFData)
import Data.Maybe (maybeToList)
import Effectful.Reader.Static (Reader, runReader, ask, local)
import Safe.Exact (zipExact)
import Data.Function ((&))
import Control.Monad ((<=<))
import Data.Traversable (forM)
import Tyck.Builtins (Builtin(..))

infer1 :: Expr -> Eff (InferenceE es) Expr
infer1 e1 = do
    reifiedE1 <- reifyHoles e1
    addLogLn $ showText reifiedE1
    weakenReader . substitute True <=< infer $ reifiedE1

check1 :: Expr -> Expr -> Eff (InferenceE es) ()
check1 e1 e2 = do
    reified1 <- reifyHoles e1
    reified2 <- reifyHoles e2
    check reified1 reified2
-- check1 e1 e2 = join $ liftA2 check (reifyHoles e1) (reifyHoles e2)

runInference :: NFData a => Eff (InferenceE '[]) a -> Eff (IOE ': '[]) (TextChain, InferenceResult a)
runInference computation =
    let resultAfterState = evalState (TyckState []) computation in
    let errorsOrResult = mapLeft showCallStack <$> runError resultAfterState in
    let resultAfterStateAlsoIOE = (inject :: Eff '[Log] a -> Eff '[Log, IOE] a) errorsOrResult in
    let resultAndLogs = runLog resultAfterStateAlsoIOE in
    let inferenceResult = resultAndLogs <&> second (\case
            Left except -> InternalCompilerError except
            Right (Left diagnostic) -> NoIce $ Diagnostic diagnostic
            Right (Right x) -> NoIce $ Ok x) in
    inferenceResult

rethrowIce :: IOE :> es => InferenceResult a -> Eff es (InferenceResultNoIce a)
rethrowIce result =
    case result of
        NoIce x -> pure x
        InternalCompilerError except -> liftIO $ throwIO except

data InferenceResult a =
    InternalCompilerError !SomeException
    | NoIce !(InferenceResultNoIce a)

data InferenceResultNoIce a =
    Ok !a
    | Diagnostic !Text
    deriving Show


-- Infer a type for an expression
infer :: Expr -> Eff (InferenceE es) Expr
infer (Hole _) = unreachableError
infer (Sort _) = pure sort
infer (ExVar _ id') = do
    result <- weakenReader $ getOneEntry (whereExId id')
    pure $ result ^?! ctxExType
infer (Var _ ix) = inject $ weakenReader $ getEntryByIx isVar ix <&> (^?! annot)
-- Inference for lambda with no annotations
-- infer (Lam _ _ _) = do
--     alpha <- allocateExistentialId
--     addToContext $ CtxExistential alpha
--     beta <- allocateExistentialId
--     addToContext $ CtxExistential beta

--     varIx <- allocateVarIx
--     addToContext $ CtxVar varIx (ExVar constO alpha)

--     removeFromContextUpTo \entry -> (entry ^? ctxVarIx) == Just varIx

--     undefined
infer arg@(Lam {}) =
    lfFoldM (arg ^?! prismExprLF)
        (\(Forall e rest body) bind -> check bind sort $> Forall e (((), bind):rest) body)
        (fmap (Forall constO []) . infer)
infer arg@(Forall {}) = checkForallWellTyped arg $> sort
infer (Apply _ func arguments) = do
    ty1 <- infer func
    application ty1 arguments
infer (Do _ stmts final) = do
    -- todo: modify doFold so that it adds bindings to the context
    tys <- doFold stmts \case
        LetF _ _ -> pure Nothing
        StmtExprF e -> Just <$> infer e
    -- lastTy <- lastMay tys & maybeToEff (throwText "empty do block")
    -- lastTy & maybeToEff (throwText "last stmt should be an expression")
    infer final
infer (Builtin _ IntType) = pure sort
infer (Builtin _ (BInt _)) = pure $ builtin IntType
infer (Builtin _ IntAdd) = pure $ forall [builtin IntType, builtin IntType] $ builtin IntType
-- infer _ = undefined

-- Applying a function of type A to e synthesizes type C
application :: Expr -> [Expr] -> Eff (InferenceE es) Expr
application arg@(Forall _ _ body) arguments =
    -- We don't have a body to zip with forall's body, so we provide Nothing
    lfZipForM (arg ^?! prismExprLF) (map Just arguments) Nothing
        (\ty (Just argument) -> check argument ty)
        (\_ Nothing -> pure ())
    $> body
application (ExVar _ funcExId') arguments = do
    -- Firstly, assign type "sort" to the func existential
    exVar <- weakenReader $ getOneEntry (whereExId funcExId')
    unify (exVar ^?! ctxExType) sort

    -- Allocate an existential for each argument
    a1Ids <- traverse (const allocateExistentialId) arguments
    let a1Type = sort
    let a1Entries = map (`CtxExistential` a1Type) a1Ids
    let a1s = map (ExVar constO) a1Ids

    -- Allocate an existential for return type
    a2Id <- allocateExistentialId
    let a2Type = sort
    let a2Entry = CtxExistential a2Id a2Type
    let a2 = ExVar constO a2Id

    replaceInContext (whereExId funcExId') \_ ->
        a1Entries <> [
            a2Entry,
            CtxExistentialAssignment funcExId' sort
                (Forall constO (padExprs a1s) a2)
        ]

    -- Fill in existentials with arguments' types
    forM_ (zipExact arguments a1s) (uncurry check)

    pure a2
application _ _ = unreachableError

-- Check that an expression has certain type
check :: Expr -> Expr -> Eff (InferenceE es) ()
-- check (Var i) ty2 = do
--     ctx <- get
--     let ty1 = (ctx ^. context) !! fromIntegral i ^?! annot
--     inferenceAssert (ty1 == ty2) "type annotated on a variable and expected type are not equal"
check lf1@(Lam {}) lf2@(Forall {}) = do
    lfZipLfForM (lf1 ^?! prismExprLF) (lf2 ^?! prismExprLF)
        (\ty1 ty2 -> do
            logContext
            -- inferenceAssert (ty1 == ty2) "type annotated on a lambda and type from forall are not equal"
            unify ty1 ty2)
        (\body1 body2 -> do
            logContext
            check body1 body2)
check (Lam {}) _ = throwText "expected a forall"
check arg@(Forall {}) (Sort _) = checkForallWellTyped arg
check (Forall {}) _ = throwText "expected sort"
-- This rule only works in Haskell, where foralls are applied implicitly
-- check subject arg@(Forall {}) =
--     lfFoldM (arg ^?! prismExprLF) (subject `check`) (\binder () -> binder `check` sort)
check expr ty2 = do
    -- Switch back to inference
    ty1 <- infer expr
    -- inferenceAssert (ty1 == ty2) (fmt "% inferred type % but expected %" [showText expr, showText ty2])
    unify ty1 ty2

checkForallWellTyped :: Expr -> Eff (InferenceE es) ()
checkForallWellTyped = traverseOf_ traversalExprExprs (`check` sort)

unify :: Expr -> Expr -> Eff (InferenceE es) ()
unify e1 e2 = do
    logContext
    reducedE1 <- inject . whnf =<< weakenReader (substitute False e1)
    reducedE2 <- inject . whnf =<< weakenReader (substitute False e2)
    go reducedE1 reducedE2
    where
        go :: Expr -> Expr -> Eff (InferenceE es) ()
        go (Sort _) (Sort _) = pure ()
        go (ExVar _ id') e22 = instantiate id' e22
        go e12 (ExVar _ id') = instantiate id' e12
        go (Var _ ix) (Var _ ix2) = inferenceAssert (ix == ix2) "mismatch"
        go (Lam {}) (Lam {}) = unreachableError
        go arg1@(Forall {}) arg2@(Forall {}) =
            let zipped = zipExact
                    (toListOf traversalExprExprs arg1)
                    (toListOf traversalExprExprs arg2) in
            mapM_ (uncurry unify) zipped
        go (Apply _ func1 args1) (Apply _ func2 args2) = do
            go func1 func2
            inferenceAssert (length args1 == length args2) "argument number mismatch"
            traverse_ (uncurry go) (zipExact args1 args2)
        go (Builtin _ b1) (Builtin _ b2) = inferenceAssert (b1 == b2) "mismatch"
        go reduced1 reduced2 = throwText $ fmt "unification error: % and %\ntheir whnf: % and %"
            [showText e1, showText e2, showText reduced1, showText reduced2]

        instantiate :: Word -> Expr -> Eff (InferenceE es) ()
        instantiate id' assignee = do
            derefedId <- weakenReader $ derefExistentialToId id'
            replaceInContext (whereExId derefedId) \(CtxExistential _ oldType) ->
                [CtxExistentialAssignment derefedId oldType assignee]

reifyHoles :: Expr -> Eff (InferenceE es) Expr
reifyHoles = cata \case
    HoleF _ -> do
        exVarTypeId <- allocateExistentialId
        addToContext $ CtxExistential exVarTypeId sort
        exVarId <- allocateExistentialId
        addToContext $ CtxExistential exVarId (ExVar constO exVarTypeId)
        pure $ ExVar constO exVarId
    ef -> embed <$> sequenceA ef

lfZipFoldM :: forall es z a. LamForall -- ^ 
  -> [z] -- ^ to be zipped with each binder
  -> z -- ^ zipped with body
  -> (a -> Expr -> z -> Eff (InferenceE es) a) -- ^ 
  -> (Expr -> z -> Eff (InferenceE es) a) -- ^ 
  -> Eff (InferenceE es) a
lfZipFoldM (GLamForall LFLam _ [] _) _ _ _ _ = throwText "lambda should have binders"
lfZipFoldM (GLamForall LFForall _ [] _) _ _ _ _ = throwText "forall should have binders"
lfZipFoldM (GLamForall _ _ binds body) toZipBinders toZipBody onBinder onBody =
    cata go (zipExact binds toZipBinders)
    where
        go :: ListF (((), Expr), z) (Eff (InferenceE es) a) -> Eff (InferenceE es) a
        go Nil = onBody body toZipBody
        go (Cons (((), bind), zipped) results) = do
            varIx <- allocateVarIx
            addToContext $ CtxVar varIx bind
            res <- results
            -- We can't just reset the context to previous state because
            -- typing functions are allowed to modify the stack both before and after
            -- the binder
            removeFromContextUpTo (whereVarIx varIx)
            onBinder res bind zipped

-- Like [lfZipFoldM] but specialized for zipping with lf
lfZipLfFoldM :: forall es a. LamForall -- ^ 
  -> LamForall -- ^ 
  -> (a -> Expr -> Expr -> Eff (InferenceE es) a) -- ^ 
  -> (Expr -> Expr -> Eff (InferenceE es) a) -- ^ 
  -> Eff (InferenceE es) a
lfZipLfFoldM lf1 (GLamForall _ _ binders body) =
    lfZipFoldM lf1 (unpadExprs binders) body

-- toListOf (prismExprLF . traversalLFExprs) arg
lfFoldM :: LamForall -- ^ 
  -> (a -> Expr -> Eff (InferenceE es) a) -- ^ 
  -> (Expr -> Eff (InferenceE es) a) -- ^ 
  -> Eff (InferenceE es) a
lfFoldM lf@(GLamForall _ _ binders _) onBinder onBody =
    lfZipFoldM lf (void binders) () (\result bind () -> onBinder result bind) (\body () -> onBody body)

lfZipForM :: forall es z. LamForall -- ^ 
  -> [z] -- ^ to be zipped with each binder
  -> z -- ^ zipped with body
  -> (Expr -> z -> Eff (InferenceE es) ()) -- ^ 
  -> (Expr -> z -> Eff (InferenceE es) ()) -- ^ 
  -> Eff (InferenceE es) ()
lfZipForM (GLamForall LFLam _ [] _) _ _ _ _ = throwText "lambda should have binders"
lfZipForM (GLamForall LFForall _ [] _) _ _ _ _ = throwText "forall should have binders"
lfZipForM (GLamForall _ _ binds body) toZipBinders toZipBody onBinder onBody =
    cata go (zipExact binds toZipBinders)
    where
        go :: ListF (((), Expr), z) (Eff (InferenceE es) ()) -> Eff (InferenceE es) ()
        go Nil = onBody body toZipBody
        go (Cons (((), bind), zipped) results) = do
            onBinder bind zipped
            varIx <- allocateVarIx
            addToContext $ CtxVar varIx bind
            () <- results
            -- We can't just reset the context to previous state because
            -- typing functions are allowed to modify the stack both before and after
            -- the binder
            removeFromContextUpTo \entry -> entry ^? ctxVarIx <&> (== varIx) & fromTrue

-- Like [lfZipForM] but specialized for zipping with lf
lfZipLfForM :: forall es. LamForall -- ^ 
  -> LamForall -- ^ 
  -> (Expr -> Expr -> Eff (InferenceE es) ()) -- ^ 
  -> (Expr -> Expr -> Eff (InferenceE es) ()) -- ^ 
  -> Eff (InferenceE es) ()
lfZipLfForM lf1 (GLamForall _ _ binders body) =
    lfZipForM lf1 (map snd binders) body

doFold :: [Stmt]
    -> (Stmt -> Eff (InferenceE es) a)
    -> Eff (InferenceE es) [a]
doFold = forM

inferenceAssert :: Error Text :> es => Bool -> Text -> Eff es ()
inferenceAssert True _ = pure ()
inferenceAssert False e = throwText e

logContext :: Eff (InferenceE es) ()
logContext = do
    addDiagnostics "Context: "
    ctx <- get <&> (^. context)
    addDiagnostics $ joinToString $ map showText $ reverse ctx
    addDiagnostics "\n"
-- logContext = addDiagnostics $ map (showText . (^. context))

addDiagnostics :: Text -> Eff (InferenceE es) ()
addDiagnostics = addLog

-- Add an entry to the context
addToContext :: ContextEntry -> Eff (InferenceE es) ()
addToContext ent = modify (context %~ (ent:))
--addToContext = modify . (context %~) . (:)

-- Locate an entry matching a predicate and replace it with a new run of entries
replaceInContext :: (ContextEntry -> Bool) -> (ContextEntry -> [ContextEntry]) -> Eff (InferenceE es) ()
replaceInContext predicate newEntriesFactory = modifyM (traverseOf context go)
    where
        go :: [ContextEntry] -> Eff (InferenceE es) [ContextEntry]
        go [] = throwText "entry not found"
        go (e:es) =
            if predicate e
            then pure (reverse (newEntriesFactory e) <> es)
            else go es <&> (e:)

-- Remove entries from context until [predicate] is satisfied inclusively
removeFromContextUpTo :: (ContextEntry -> Bool) -> Eff (InferenceE es) ()
removeFromContextUpTo predicate = modifyM (traverseOf context go)
    where
        go :: [ContextEntry] -> Eff (InferenceE es) [ContextEntry]
        go [] = throwText "entry not found"
        go (e:es) =
            if predicate e
            then pure es
            else go es

findNextId :: (ContextEntry -> Maybe Word) -> Eff (InferenceE es) Word
findNextId extractId = do
    -- Using flatmap
    entries <- get <&> (^. context) <&> (>>= (extractId >>> maybeToList))
    pure $ maybe 0 (+1) (maximumMay entries)

allocateVarIx :: Eff (InferenceE es) Word
allocateVarIx = findNextId (^? ctxVarIx)

allocateExistentialId :: Eff (InferenceE es) Word
allocateExistentialId = findNextId (^? ctxExId)

-- Replace all existentials with their values
substitute :: Bool -> Expr -> Eff (Reader TyckState ': Error Text ': es) Expr
substitute failOnUninstantiated =
    let onUninstantiated =
            if failOnUninstantiated
            then const $ throwText "existential not instantiated"
            else (embed <$>) . sequenceA in
    cata \case {
        arg@(ExVarF _ id') -> derefExistential id' >>= maybe (onUninstantiated arg) pure;
        ef -> embed <$> sequenceA ef
    }

eraseNames :: NamefulExpr -> Eff '[Error Text] Expr
eraseNames = runReader [] . cata go
    where
        go :: GExprF 'Parsed (Eff '[Reader [Text], Error Text] Expr) -> Eff '[Reader [Text], Error Text] Expr
        go (VarF _ name) = do
            binds <- ask
            ix <- fromJustText $ wordFindIndex (== name) binds
            pure $ Var constO ix
        go (toLamForall -> Just lf) = processLF lf <&> (fromLamForall >>> embed)
        go arg = do
            unArg <- sequenceA arg
            doeg <- raise $ mapNoNames unArg
            pure $ embed doeg

        processLF :: GLamForall 'Parsed (Eff '[Reader [Text], Error Text] Expr) -> Eff '[Reader [Text], Error Text] (GLamForall 'Debruijn Expr)
        processLF (GLamForall tag _ binders body) = do
            (binders2, body2) <- foldr (\(name, ty) next -> do
                        unAnnot <- ty
                        result <- local (name :) next
                        let (binders2, body2) = result
                        pure (((), unAnnot) : binders2, body2))
                    (([],) <$> body) binders
            pure $ GLamForall tag constO binders2 body2

        mapNoNames :: GExprF 'Parsed a -> Eff '[Error Text] (GExprF 'Debruijn a)
        mapNoNames = fromJustText . gExprTraverse Just (const Nothing) (const Nothing)
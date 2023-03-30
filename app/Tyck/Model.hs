{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use view" #-}
-- {-# LANGUAGE DeriveDataTypeable #-}

module Tyck.Model where

import Control.Applicative (Applicative (liftA2), Const)
import Control.Lens (Prism', Traversal', prism', traversal, forMOf, makePrisms, (^.), (^?), traverseOf, (??))
import Control.Lens.TH (makeLenses)
import Data.Functor ( (<&>) )
import Data.Functor.Foldable (Base, Corecursive, Recursive)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Text (Text, append)
import Util.ShowText (ShowText (..), showFromShowText)
import Util.Util (fmt, joinToString, constO, genericAtMay, throwText, unreachableError, fromTrue, unsingletonExact, eitherToError, joinToString', maybeToEff, baseIso)
import Effectful (Eff, raise)
import Effectful.State.Static.Local (evalState, get, modify, State, runState)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Control.Lens.Extras (is)
import Effectful.Error.Static (Error, HasCallStack)
import Util.Log (Log)
import Data.Function ((&))
import Effectful.Reader.Static (Reader, ask)
import Control.Arrow ((>>>))
import Control.Lens.Tuple (_1)
import Tyck.Builtins (Builtin)
import Data.Traversable (forM)

-- import Data.Functor.Foldable.TH

data CompilerStage = Parsed | Debruijn | Typed

type family SInferredType (d :: CompilerStage) :: Type -> Type where
    SInferredType 'Parsed = Const ()
    SInferredType 'Debruijn = Const ()
    SInferredType 'Typed = Identity
type family SBinderName (d :: CompilerStage) :: Type where
    SBinderName 'Parsed = Text
    SBinderName 'Debruijn = ()
    SBinderName 'Typed = ()
type family SVar (d :: CompilerStage) :: Type where
    SVar 'Parsed = Text
    SVar 'Debruijn = Word
    SVar 'Typed = ()

-- Samodiy expression parametrized by stage
data GExpr d =
    Hole { _inferredType :: !(SInferredType d (GExpr d)) }
    | Sort { _inferredType :: !(SInferredType d (GExpr d)) }
    | ExVar { _inferredType :: !(SInferredType d (GExpr d)), _exprExIx :: !Word }
    -- Use de Bruijn indices
    | Var { _inferredType :: !(SInferredType d (GExpr d)), _exprIx :: !(SVar d) }
    -- Variable binders may include names for pretty-printing
    | Lam { _inferredType :: !(SInferredType d (GExpr d)), _exprBinders :: ![(SBinderName d, GExpr d)], _exprBody :: !(GExpr d) }
    | Forall { _inferredType :: !(SInferredType d (GExpr d)), _exprBinders :: ![(SBinderName d, GExpr d)], _exprBody :: !(GExpr d) }
    | Apply { _inferredType :: !(SInferredType d (GExpr d)), _exprFunc :: !(GExpr d), _exprArgs :: ![GExpr d] }
    | Do { _inferredType :: !(SInferredType d (GExpr d)), _doBody :: ![GStmtF d (GExpr d)], _doFinal :: !(GExpr d) }
    | Builtin { _inferredType :: !(SInferredType d (GExpr d)), _exprBuiltin :: !Builtin }

data GStmtF d e =
    LetF { _letName :: !(SBinderName d), _letInitializer :: !e }
    | StmtExprF { _stmtExpr :: !e }
    deriving (Functor, Foldable, Traversable)

makeLenses ''GExpr
makePrisms ''GStmtF

deriving instance Generic (GExpr d)
deriving instance Generic (GExprF d (GExpr d))
deriving instance Generic (GStmtF d (GExpr d))

deriving instance (Eq (SInferredType d (GExpr d)),
    Eq (SBinderName d),
    Eq (SVar d),
    Eq (GStmtF d (GExpr d))) =>
    Eq (GExpr d)

deriving instance (Eq (SInferredType d (GExpr d)),
    Eq (SBinderName d),
    Eq (SVar d)) =>
    Eq (GStmtF d (GExpr d))

-- Expanded: makeBaseFunctor ''GExpr
data GExprF (d :: CompilerStage) r
  = HoleF {_inferredTypeF :: !(SInferredType d r)} |
    SortF {_inferredTypeF :: !(SInferredType d r)} |
    ExVarF {_inferredTypeF :: !(SInferredType d r),
            _exprExIxF :: !Word} |
    VarF {_inferredTypeF :: !(SInferredType d r),
          _exprIxF :: !(SVar d)} |
    LamF {_inferredTypeF :: !(SInferredType d r),
          _exprBindersF :: ![(SBinderName d, r)],
          _exprBodyF :: !r} |
    ForallF {_inferredTypeF :: !(SInferredType d r),
             _exprBindersF :: ![(SBinderName d, r)],
             _exprBodyF :: !r} |
    ApplyF {_inferredTypeF :: !(SInferredType d r),
            _exprFuncF :: !r,
            _exprArgsF :: ![r]} |
    DoF {_inferredTypeF :: !(SInferredType d r),
            _doBodyF :: ![GStmtF d r],
            _doFinalF :: !r} |
    BuiltinF {_inferredTypeF :: !(SInferredType d r),
            _exprBuiltinF :: !Builtin}
deriving instance (Functor (SInferredType d)) => Functor (GExprF d)
deriving instance (Foldable (SInferredType d)) => Foldable (GExprF d)
deriving instance (Traversable (SInferredType d)) => Traversable (GExprF d)
type instance Base (GExpr d) = GExprF d
instance (Functor (SInferredType d)) => Recursive (GExpr d) where
instance (Functor (SInferredType d)) => Corecursive (GExpr d) where

-- GExprF is functorial in stage
gExprMap :: forall d1 d2 x. (Functor (SInferredType d1)) =>
    (forall a. SInferredType d1 a -> SInferredType d2 a) ->
    (SBinderName d1 -> SBinderName d2) ->
    (SVar d1 -> SVar d2) ->
    GExprF d1 x -> GExprF d2 x
gExprMap inferredTypeF nameF referenceF = runIdentity . gExprTraverse
    (Identity . inferredTypeF)
    (Identity . nameF)
    (Identity . referenceF)

gExprTraverse :: forall d1 d2 f x. (Applicative f, Functor (SInferredType d1)) =>
    (forall a. SInferredType d1 a -> f (SInferredType d2 a)) ->
    (SBinderName d1 -> f (SBinderName d2)) ->
    (SVar d1 -> f (SVar d2)) ->
    GExprF d1 x -> f (GExprF d2 x)
gExprTraverse inferredTypeF nameF referenceF = go
    where
        go :: GExprF d1 x -> f (GExprF d2 x)
        go (HoleF e) = HoleF <$> inferredTypeF e
        go (SortF e) = SortF <$> inferredTypeF e
        go (ExVarF e id') = ExVarF <$> inferredTypeF e ?? id'
        go (VarF e ix) = VarF <$> inferredTypeF e <*> referenceF ix
        go (LamF e xs body) = LamF <$> inferredTypeF e <*> traverse (traverseOf _1 nameF) xs ?? body
        go (ForallF e xs body) = ForallF <$> inferredTypeF e <*> traverse (traverseOf _1 nameF) xs ?? body
        go (ApplyF e fun args) = ApplyF <$> inferredTypeF e ?? fun ?? args
        go (DoF e stmts final) = DoF <$> inferredTypeF e <*> traverse (gStmtTraverse nameF) stmts ?? final
        go (BuiltinF e b) = BuiltinF <$> inferredTypeF e ?? b

gStmtTraverse :: forall d1 d2 f x. (Applicative f) =>
    (SBinderName d1 -> f (SBinderName d2)) ->
    GStmtF d1 x -> f (GStmtF d2 x)
gStmtTraverse nameF = go
    where
        go :: GStmtF d1 x -> f (GStmtF d2 x)
        go (LetF name initializer) = LetF <$> nameF name ?? initializer
        go (StmtExprF expr) = pure (StmtExprF expr)

-- Expression with named variables
type NamefulExpr = GExpr 'Parsed

-- Expression with unnamed variables
type Expr = GExpr 'Debruijn

-- Expression with its type
type TypedExpr = GExpr 'Typed

-- Statement with named variables
type NamefulStmt = GStmtF 'Parsed NamefulExpr

-- Statement with unnamed variables
type Stmt = GStmtF 'Debruijn Expr

-- Statement with its type
type TypedStmt = GStmtF 'Typed TypedExpr

padExprs :: Functor t => t Expr -> t ((), Expr)
padExprs = fmap ((),)

unpadExprs :: [((), Expr)] -> [Expr]
unpadExprs = map snd

hole :: Expr
hole = Hole constO

-- Expr constructors
sort :: Expr
sort = Sort constO

var :: Word -> Expr
var = Var constO

lam :: [Expr] -> Expr -> Expr
lam xs = Lam constO (padExprs xs)

forall :: [Expr] -> Expr -> Expr
forall xs = Forall constO (padExprs xs)

apply :: Expr -> [Expr] -> Expr
apply = Apply constO

do_ :: [Stmt] -> Expr -> Expr
do_ = Do constO

builtin :: Builtin -> Expr
builtin = Builtin constO

-- sortTyped :: TypedExpr
-- sortTyped = fix (Sort . Identity)

-- newtype Nameful e = Nameful { unNameful :: (Text, e) }

-- equalsIgnoreName :: NamefulExpr -> NamefulExpr -> Bool
-- equalsIgnoreName e1 e2 = eraseNames e1 == eraseNames e2

-- deriving instance Data Expr


-- deriving instance Generic Stmt
-- deriving instance Generic Expr
instance NFData Stmt
instance NFData Expr

instance (ShowText (SBinderName d), ShowText (SVar d)) => ShowText (GExpr d) where
    showText (Hole _) = "_"
    showText (Sort _) = "Sort"
    showText (ExVar _ id') = "e" `append` showText id'
    showText (Var _ ix) = "x" `append` showText ix
    showText (Lam _ binds body) =
        fmt "(fun(%) => %)" [joinToString $ map pairToText binds, showText body]
    showText (Forall _ binds body) =
        fmt "(for(%), %)" [joinToString $ map pairToText binds, showText body]
    showText (Apply _ fun args) =
        fmt "%(%)" [showText fun, joinToString $ map showText args]
    showText (Do _ stmts final) =
        fmt "do\n%\nend" [joinToString' "\n" $ map showText stmts ++ [showText final]]
    showText (Builtin _ b) = showText b

instance (ShowText (SBinderName d), ShowText (SVar d)) => ShowText (GStmtF d (GExpr d)) where
    showText (LetF name initializer) =
        fmt "let % = %" [showText name, showText initializer]
    showText (StmtExprF expr) = showText expr

instance (ShowText (GExpr d)) => Show (GExpr d) where
    show = showFromShowText

-- instance ShowText (GExpr b) where
--     showText (Int n) = showText n
--     showText IntType = "Int"
--     showText Sort = "Sort"
--     showText (Var i) = "x" `append` showText i
--     showText (Lam binds body) =
--         fmt "fun % => %" [joinToString $ map pairToText binds, showText body]
--     showText (Forall binds body) =
--         fmt "forall %, %" [joinToString $ map pairToText binds, showText body]
--     showText (Apply fun args) =
--         fmt "%(%)" [showText fun, joinToString' " " $ map showText args]

-- instance Eq Expr where
--     (==) (Int n) (Int m) = n == m
--     (==) IntType IntType = True
--     (==) Sort Sort = True
--     (==) (Var i) (Var j) = i == j
--     -- Ignore variable names
--     (==) (Lam xs body1) (Lam ys body2) = all (id) $ zipExact xs ys

pairToText :: (ShowText n, ShowText (GExpr d)) => (n, GExpr d) -> Text
pairToText (name1, annot1) = fmt "%: %" [showText name1, showText annot1]

data LFTag = LFLam | LFForall

data GLamForall d e = GLamForall !LFTag !(SInferredType d e) ![(SBinderName d, e)] !e

-- A type isomorphic to lambda and forall
type LamForall = GLamForall 'Debruijn Expr
-- makeLenses ''LamForall

-- traverseExprLf :: Applicative f => GExprF d1 e1 -> (GLamForall d1 e1 -> f (GLamForall d2 e2)) -> Maybe (f (GExprF d2 e2))
-- traverseExprLf (LamF e binders body) k = traverseExprLfHelper $ k (GLamForall LFLam e binders body)
-- traverseExprLf (ForallF e binders body) k = traverseExprLfHelper $ k (GLamForall LFForall e binders body)
-- traverseExprLf _ _ = Nothing

-- traverseExprLfHelper :: Applicative f => f (GLamForall d e) -> Maybe (f (GExprF d e))
-- traverseExprLfHelper = Just . ((^. re prismExprGLF) <$>)

-- unsafeTraversalExprLf :: Traversal (GExprF d1 e1) (GExprF d2 e2) (GLamForall d1 e1) (GLamForall d2 e2)
-- unsafeTraversalExprLf = traversal go
--     where
--         go :: Applicative f => (GLamForall d1 e1 -> f (GLamForall d2 e2)) -> GExprF d1 e1 -> f (GExprF d2 e2)
--         go k arg = arg ^?! prismExprGLF & k <&> (^. re prismExprGLF)

prismExprGLF :: Prism' (GExprF d e) (GLamForall d e)
prismExprGLF = prism' fromLamForall toLamForall

fromLamForall :: GLamForall d e -> GExprF d e
fromLamForall (GLamForall LFLam e binds body) = LamF e binds body
fromLamForall (GLamForall LFForall e binds body) = ForallF e binds body

toLamForall :: GExprF d e -> Maybe (GLamForall d e)
toLamForall (LamF e binds body) = Just $ GLamForall LFLam e binds body
toLamForall (ForallF e binds body) = Just $ GLamForall LFForall e binds body
toLamForall _ = Nothing

prismExprLF :: Prism' Expr LamForall
prismExprLF = baseIso . prismExprGLF

traversalLFExprs :: Traversal' LamForall Expr
traversalLFExprs = traversal go
    where
        go :: Applicative f => (Expr -> f Expr) -> LamForall -> f LamForall
        go k (GLamForall t e binds body) = liftA2 (GLamForall t e)
            (traverse (padExprs . k) (unpadExprs binds))
            (k body)

traversalExprExprs :: Traversal' Expr Expr
traversalExprExprs = prismExprLF . traversalLFExprs

-- l42 :: Lens' LamForall [Expr]
-- l42 = lens getExprs setExprs
--     where
--         getExprs (GLamForall _ _ binds body) = fmap snd binds `snoc` body
--         setExprs (GLamForall t e _ _) xs =
--             let (binds, body) = fromJust $ viewR xs in
--             GLamForall t e (fmap ((),) binds) body

-- forAccumMLF :: s -> (s -> Expr -> Eff es (s, Expr)) -> LamForall -> Eff es LamForall
-- forAccumMLF start f lf =
--     evalState start $ forMOf traversalLFExprs lf (\expr1 -> do {
--         stateM (\st -> raise $ swap <$> f st expr1)
--     })

forCountingMLF :: Word -> (Word -> Expr -> Eff es Expr) -> LamForall -> Eff es LamForall
forCountingMLF start k lf = evalState start $ forMOf traversalLFExprs lf $ \expr1 -> do
    i <- get
    modify ((+1) :: Word -> Word)
    raise $ k i expr1

forIndexedMLF :: (Word -> Expr -> Eff es Expr) -> LamForall -> Eff es LamForall
forIndexedMLF = forCountingMLF 0

forCountingMDo :: Word ->
    (Word -> Stmt -> Eff es Stmt) ->
    (Word -> Expr -> Eff es Expr) ->
    GExprF 'Debruijn Expr ->
    Eff es Expr
forCountingMDo start k onFinal (DoF _ stmts final) = do
    (result, n) <- runState start $ forM stmts $ \stmt -> do
            i <- get
            case stmt of
                LetF () _ -> modify ((+1) :: Word -> Word)
                StmtExprF _ -> pure ()
            raise $ k i stmt
    Do constO result <$> onFinal n final
forCountingMDo _ _ _ _ = undefined

-- foldMDo :: GExprF d1 t -> GExpr d2
-- foldMDo (DoF _ stmts final) =
--     let (cutoff1, result) = foldl' (\(cutoff, acc) -> \case
--             LetF () ini -> (cutoff + 1, LetF () (shift i c ini) : acc)
--             StmtExprF e -> (cutoff, StmtExprF (shift i c e) : acc)) (0, []) stmts in
--     Do constO (reverse result) (shift i cutoff1 final)
-- foldMDo _ = undefined


-- The Г typing context as used in the paper
data ContextEntry =
    -- Introduce a variable binder
    CtxVar { _ctxVarIx :: !Word, _annot :: !Expr }
    | CtxExistential { _ctxExId :: !Word, _ctxExType :: !Expr }
    | CtxExistentialAssignment { _ctxExId :: !Word, _ctxExType :: !Expr, _value :: !Expr }
    deriving (Eq{-, Data-})
makeLenses ''ContextEntry
makePrisms ''ContextEntry

instance ShowText ContextEntry where
    showText (CtxVar ix ann) = fmt "var %: %" [showText ix, showText ann]
    showText (CtxExistential id' ann) = fmt "exi %: %" [showText id', showText ann]
    showText (CtxExistentialAssignment id' ann val) = fmt "exi %: % = %" [showText id', showText ann, showText val]

isVar :: ContextEntry -> Bool
isVar = is _CtxVar
--isVar x = toConstr x == toConstr (CtxVar 0 sort)
--isVar x = isTrue# (dataToTag# x ==# dataToTag# (CtxVar 0 sort))

whereExId :: Word -> ContextEntry -> Bool
whereExId id' = (^? ctxExId) >>> fmap (== id') >>> fromTrue

whereVarIx :: Word -> ContextEntry -> Bool
whereVarIx ix = (^? ctxVarIx) >>> fmap (== ix) >>> fromTrue

newtype TyckState = TyckState {
    _context :: [ContextEntry]
}
makeLenses ''TyckState

contextEntries :: Traversal' TyckState ContextEntry
contextEntries = traversal (traverseOf context . traverse)

-- Effect of the inference functions
type InferenceE es = State TyckState ': Error Text ': Log ': es

getEntryByIx :: (ContextEntry -> Bool) -> Word -> Eff (Reader TyckState ': Error Text ': es) ContextEntry
getEntryByIx predicate i = do
    variables <- filterContext predicate
    variables `genericAtMay` i & maybeToEff (throwText "entry not found")

derefExistentialToId :: Word -> Eff (Reader TyckState ': Error Text ': es) Word
derefExistentialToId id' = do
    variable <- getOneEntry (whereExId id')
    case variable of
        -- Recurse until terminal assignment
        CtxExistentialAssignment _ _ (ExVar _ nextId) -> derefExistentialToId nextId
        CtxExistentialAssignment resultId _ _ -> pure resultId
        CtxExistential resultId _ -> pure resultId
        _ -> unreachableError

derefExistential :: HasCallStack => Word -> Eff (Reader TyckState ': Error Text ': es) (Maybe Expr)
derefExistential id' = do
    derefedId <- derefExistentialToId id'
    exVar <- getOneEntry (whereExId derefedId)
    case exVar of
        CtxExistentialAssignment _ _ val -> pure $ pure val
        CtxExistential _ _ -> pure Nothing
        _ -> unreachableError

-- getContext :: Eff (InferenceE es) [ContextEntry]
-- getContext = get <&> (^. context)

filterContext :: (ContextEntry -> Bool) -> Eff (Reader TyckState ': Error Text ': es) [ContextEntry]
filterContext predicate = ask <&> (^. context) <&> filter predicate

getOneEntry :: HasCallStack => (ContextEntry -> Bool) -> Eff (Reader TyckState ': Error Text ': es) ContextEntry
getOneEntry predicate = do
    results <- filterContext predicate
    eitherToError $ unsingletonExact results
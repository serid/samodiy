-- {-# LANGUAGE TypeApplications #-}

module Future where

-- import Control.Monad.Trans.State.Strict (StateT (..))
-- import Data.Coerce (coerce)
-- import Data.Tuple (swap)

-- -- From https://hackage.haskell.org/package/base-4.18.0.0/docs/src/Data.Traversable.html#mapAccumM
-- mapAccumM ::
--   forall m t s a b.
--   (Monad m, Traversable t) =>
--   (s -> a -> m (s, b)) ->
--   s ->
--   t a ->
--   m (s, t b)
-- mapAccumM f s t = swap <$> coerce (mapM @t @(StateT s m) @a @b) (StateT . flip (\x y -> fmap swap (f x y))) t s
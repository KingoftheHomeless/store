module Control.Comonad.State where
import Control.Comonad
import Control.Monad.State

{-
instance Monoid s => Comonad (State s) where
    extract m = fst $ runState m mempty
    duplicate m = state $ \s -> (state $ \t -> runState m (mappend s t), snd $ runState m s)
-}

-- This is also a complete spitball.
instance (Monoid s, Comonad w) => Comonad (StateT s w) where
    extract m = fst . extract $ runStateT m mempty
    duplicate (StateT m) = StateT $ \s -> fmap (\(_, s') -> (StateT $ \t -> m (mappend s t), s')) (m s)
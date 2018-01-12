{-# LANGUAGE FunctionalDependencies, FlexibleInstances, FlexibleContexts, DefaultSignatures, TupleSections, RankNTypes #-}
module Control.Monad.Store.Class where
import              Data.Monoid
import              Control.Applicative
import              Control.Comonad.Store hiding (store, runStore)
import qualified    Control.Comonad.Store as Str
import              Control.Monad.Co
import              Control.Monad.State

class MonadStore s m | m -> s where
    store :: (s -> a) -> s -> m a
    default store :: (Applicative m, Monoid s) => (s -> a) -> s -> m a
    store f m = write m *> liftStore f

    -- Causes s to be appended to the stored value during writing.
    write :: s -> m ()
    write = store (const ())

    -- If in the reading stage, reads the stored value. Otherwise reads mempty.
    scry :: Monoid s => m s
    scry = store id mempty

    -- Promotes a function to a MonadStore
    liftStore :: Monoid s => (s -> a) -> m a
    liftStore = (`store` mempty)

    -- appends s after the value stored in the MonadStore
    writeAfter :: Monoid s => m a -> s -> m a
    default writeAfter :: (Monoid s, Applicative m) => m a -> s -> m a
    writeAfter m s = m <* write s

    -- appends s before the value stored in the MonadStore
    writeBefore :: Monoid s => m a -> s -> m a
    default writeBefore :: (Monoid s, Applicative m) => m a -> s -> m a
    writeBefore m s = write s *> m

instance Monoid s => Comonad (State s) where
    extract m = fst $ runState m mempty
    duplicate m = state $ \s -> (state $ \t -> runState m (mappend s t), snd $ runState m s)

 
instance Monoid s => Monad (Store s) where
    m >>= k = Str.store (\s -> peek s (k (peek s m ))) (pos m `mappend` pos (k (peek mempty m)))

    
newtype CS s a = CS { unCS :: Co (State s) (s -> a) }

instance Functor (CS s) where
    fmap f (CS m) = CS $ (fmap . fmap) f m

instance Monoid s => Applicative (CS s) where
    pure            = CS . pure . pure
    CS f <*> CS a   = CS $ liftA2 (<*>) f a
    
instance Monoid s => Monad (CS s) where
    m >>= f = f (runCS' m) --m >>= unCS . f . ($ mempty)
    

split :: CS s a -> (s -> a, s)
split = (`runCo` (state $ \st -> ((, st), st))). unCS

runCS' :: CS s a -> a
runCS' = (\(f, a) -> f a) . split

runCS :: Co (State s) a -> a
runCS = (`runCo` (pure id))
,

runStore :: Store s a -> a
runStore str = peek (pos str) str

-- Co (forall r. w (a -> r) -> r)

convert :: Monoid s => CS s a -> Store s a
convert = uncurry Str.store . split

convert' :: forall s a. Monoid s => Store s a -> CS s a
convert' str = CS (co marriza)
    where
        marriza st =
            let
                (_, a') = runState st (pos str)
                (f', _) = runState st (a' <> pos str)
            in
                f' $ (`peek` str)



cnv :: Monoid s => Store s a -> Co (State s) a
cnv str = co marriza
    where
        marriza st =
            let
                (_, a') = runState st mempty
                (f', _) = runState st (a' <> pos str) -- (a' <> pos str) -- $ a' --pos str --mempty --(a' <> pos str)
            in
                f' $ peek (a' <> pos str) str

instance Monoid s => MonadStore s (CS s) where
    store f s = convert' $ Str.store f s

instance Monoid s => MonadStore s (Co (State s)) where
    store f s = cnv $ Str.store f s

instance Monoid s => MonadStore s (Store s) where
    store = Str.store
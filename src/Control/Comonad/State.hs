{-# LANGUAGE FlexibleInstances #-}
module Control.Comonad.State where
import Control.Comonad
import Control.Monad.State


instance Monoid s => Comonad (State s) where
    extract m = fst $ runState m mempty
    duplicate m = state $ \s -> (state $ \t -> runState m (mappend s t), snd $ runState m s)

newtype StateCT s w a = StateCT { unStateCT :: w (s -> (a, s)) }

instance Functor w => Functor (StateCT s w) where
    fmap f (StateCT m) = StateCT $ fmap ((\ ~(a, s) -> (f a, s)) .) m

instance (Monoid s, Comonad w) => Comonad (StateCT s w) where
    extract = fst . ($ mempty) . extract . unStateCT
    extend f = StateCT . extend (\wf m -> (f (StateCT (fmap (. mappend m) wf)), snd $ extract wf m)) . unStateCT

{-
extend extract = id
    extend f m = StateCT $ extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
    extend extract m = StateCT $ extend (\wf s -> (extract (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (extract (StateCT (fmap (. mappend s) wf)), snd $ extract wf s) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst . ($ mempty) . extract . unStateCT $ (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst . ($ mempty) . extract $ fmap (. mappend s) wf), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract . fmap (. mappend s)) wf), snd $ extract wf s)) (unStateCT m)
        -- extract . fmap f = f . extract
    = StateCT $ extend (\wf s -> (fst . ($ mempty) $ ((. mappend m) . extract) wf), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract wf) (. mappend s), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract wf . mappend s), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst $ extract wf (mappend s mempty), snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> (fst $ extract wf s, snd $ extract wf s)) (unStateCT m)
    = StateCT $ extend (\wf s -> extract wf s) (unStateCT m)
    = StateCT $ extend extract (unStateCT m)
    = StateCT $ unStateCT m
    = m
    
extract . extend f = f
        extend f m = StateCT $ extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
        extract (extend f m) = fst . ($ mempty) . extract . unStateCT $ StateCT $ extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
        = fst . ($ mempty) . extract $ extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)   
        = fst . ($ mempty) $ (extract . extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s))) (unStateCT m)
            -- extract . extend f = f
        = fst . ($ mempty) $ (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) (unStateCT m)
        = fst . ($ mempty) $ (\s -> (f (StateCT (fmap (. mappend s) (unStateCT m))), snd $ extract (unStateCT m) s))
        = fst $ (f (StateCT (fmap (. mappend mempty) (unStateCT m))), snd $ extract (unStateCT m) mempty)
        = f (StateCT (fmap (. mappend mempty) (unStateCT m)))
        = f (StateCT (fmap (. id) (unStateCT m)))
        = f (StateCT (fmap id (unStateCT m)))
        = f (StateCT (unStateCT m))
        = f m
-}
    
{-
-- This most likely doesn't work.
instance (Monoid s, Comonad w) => Comonad (StateT s w) where
    extract m = fst . extract $ runStateT m mempty
    duplicate (StateT m) = StateT $ \s -> fmap (\(_, s') -> (StateT $ \t -> m (mappend s t), s')) (m s)
    
-}
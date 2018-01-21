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
    extend f = StateCT . extend (\wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)) . unStateCT

{-

(StateCT s w) is a comonad.

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

extend f . extend g = extend (f . extend g)
    let help fun = \wf s -> (f (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)

    extend f (extend g m) = StateCT $ extend (help f) (unStateCT (StateCT $ extend (help g) (unStateCT m)))
            -- unStateCT . StateCT = id
        = StateCT $ extend (help f) (extend (help g) (unStateCT m))
        = StateCT $ (extend (help f) . extend (help g)) (unStateCT m)
            -- extend f . extend g = extend (f . extend g)
        = StateCT $ (extend (help f . extend (help g))) (unStateCT m)
            -- expansion
        = StateCT $ extend (\wf s -> help f (extend (help g) wf) s) (unStateCT m)

        -- we'll now study subexpression

        (\wf s -> help f (extend (help g) wf) s)
        = \wf s -> (f (StateCT (fmap (. mappend s) (extend (help g) wf))), snd $ extract (extend (help g) wf) s)
        = \wf s -> (..., snd $ extract (extend (help g) wf) s)
            -- extract . extend f = f
        = \wf s -> (..., snd $ (help g) wf s)
        = \wf s -> (..., snd $ (\wf' s' -> (..., snd $ extract wf' s') wf s)
        = \wf s -> (..., snd $ (..., snd $ extract wf s))
        = \wf s -> (..., snd $ extract wf s)
        = \wf s -> (f (StateCT (fmap (. mappend s) (extend (help g) wf))), ...)
            -- fmap f = extend (f . extract)
        = \wf s -> (f (StateCT (extend ((. mappend s) . extract) (extend (help g) wf))), ...)
            -- extend f . extend g = extend (f . extend g)
        = \wf s -> (f (StateCT (extend ((. mappend s) . extract . extend (help g)) wf)), ...)
            -- extract . extend f = f
        = \wf s -> (f (StateCT (extend ((. mappend s) . help g) wf)), ...)

        -- we'll now study subexpression
        (. mappend s) . help g
        = \wf' -> help g wf' . mappend s
        = \wf' s' -> help g wf' (mappend s s')

        -- thus
        (\wf s -> help f (extend (help g) wf) s)
        = \wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), ...)
        = \wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)

        --thus
        extend f (extend g m)
        = StateCT $ extend (\wf s -> help f (extend (help g) wf) s) (unStateCT m)
        = StateCT $ extend (\wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)) (unStateCT m)


    extend (f . extend g) m = StateCT $ extend (help (f . extend g)) (unStateCT m)
            -- expand definition of extend
        = StateCT $ extend (help (f . StateCT . extend (help g) . unStateCT)) (unStateCT m)
            -- expansion
        = StateCT $ extend (\wf s -> help (f . StateCT . extend (help g) . unStateCT) wf s) (unStateCT m)

        -- we'll now study subexpression
        (\wf s -> help (f . StateCT . extend (help g) . unStateCT) wf s)
            -- expand definition of help
        = \wf s -> ((f . StateCT . extend (help g) . unStateCT) (StateCT (fmap (. mappend s) wf)), snd $ extract wf s)
            -- unStateCT . StateCT = id
        = \wf s -> ((f . StateCT . extend (help g) . fmap (. mappend s)) wf, snd $ extract wf s)
            -- because
            -- fmap f = extend (f . extract)
            -- and
            -- extend f . extend g = extend (f . extend g)
            -- therefore
            -- extend f . fmap g = extend (f . fmap g)
        = \wf s -> ((f . StateCT . extend (help g . fmap (. mappend s))) wf, ...)
            -- apply wf
        = \wf s -> (f (StateCT (extend (help g . fmap (. mappend s)) wf)), ...)

        -- we'll now study subexpression
        help g . fmap (. mappend s)
            -- expand
        = \wf' s' -> help g (fmap (. mappend s) wf') s'
            -- expand definition of help
        = \wf' s' -> (f (StateCT (fmap (. mappend s') (fmap (. mappend s) wf'))), snd $ extract (fmap (. mappend s) wf') s')
        = \wf' s' -> (..., snd $ extract (fmap (. mappend s) wf') s')
            -- extract . fmap f = f . extract
        = \wf' s' -> (..., snd $ (. mappend s) (extract wf') s')
        = \wf' s' -> (..., snd $ (extract wf' . mappend s) s')
        = \wf' s' -> (..., snd $ extract wf' (mappend s s'))
        = \wf' s' -> (f (StateCT (fmap (. mappend s') (fmap (. mappend s) wf'))), ...)
            -- fmap f . fmap g = fmap (f . g)
        = \wf' s' -> (f (StateCT (fmap ((. mappend s') . (. mappend s)) wf')), ...)

        -- we'll now study subexpression
        (. mappend s') . (. mappend s)
            -- expand
        = \st -> (. mappend s') ((. mappend s) st)
            -- apply
        = \st -> st . mappend s . mappend s'
            -- expand
        = \st s'' -> st (mappend s (mappend s' s''))
            -- mappend x (mappend y z) = mappend (mappend x y) z
        = \st s'' -> st (mappend (mappend s s') s'')
            -- make point-free
        = \st -> st . mappend (mappend s s')
        = (. mappend (mappend s s'))

        -- thus
        help g . fmap (. mappend s)
        = \wf' s' -> (g (StateCT (fmap ((. mappend s') . (. mappend s)) wf')), ...)
        = \wf' s' -> (g (StateCT (fmap (. mappend (mappend s s')) wf')), ...)
        = \wf' s' -> (g (StateCT (fmap (. mappend (mappend s s')) wf')), snd $ extract wf' (mappend s s'))
            -- collapse this to a use of help
        = \wf' s' -> help g wf' (mappend s s')

        -- thus
        (\wf s -> help (f . StateCT . extend (help g) . unStateCT) wf s)
        = \wf s -> (f (StateCT (extend (help g . fmap (. mappend s)) wf)), ...)
        = \wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), ...)
        = \wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)

        -- thus
        extend (f . extend g) m
        = StateCT $ extend (\wf s -> help (f . StateCT . extend (help g) . unStateCT) wf s) (unStateCT m)
        = StateCT $ extend (\wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)) (unStateCT m)


        
    extend f (extend g m)
        = StateCT $ extend (\wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)) (unStateCT m)

    extend (f . extend g) m
        = StateCT $ extend (\wf s -> (f (StateCT (extend (\wf' s' -> help g wf' (mappend s s')) wf)), snd $ extract wf s)) (unStateCT m)

    extend f . extend g = extend (f . extend g)
-}

{-  
-- This most likely doesn't work.
instance (Monoid s, Comonad w) => Comonad (StateT s w) where
    extract m = fst . extract $ runStateT m mempty
    duplicate (StateT m) = StateT $ \s -> fmap (\(_, s') -> (StateT $ \t -> m (mappend s t), s')) (m s)
    
-}
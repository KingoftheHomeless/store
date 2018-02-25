{-# LANGUAGE TupleSections, DeriveFunctor, FlexibleInstances #-}
module Control.Comonad.Update where

-- The update comonad transformer.
-- "UpdateCT p s w" is a comonad as long as s is a monoid (and w is a comonad).

import Data.Monoid.Action
import Data.Semigroup
import Control.Applicative
import Control.Comonad
import Control.Monad.Identity

-- There's a monad transfomer version of Update too, which is well known.
newtype UpdateCT p s w a = UpdateCT { runUpdateCT :: w (s -> (a, p)) } deriving (Functor)

type Update p s = UpdateCT p s Identity

update :: (s -> (a, p)) -> Update p s a
update = UpdateCT . Identity

runUpdate :: Update p s a -> s -> (a, p)
runUpdate = runIdentity . runUpdateCT

instance (Semigroup p, Monoid p, Action p s, Applicative w) => Applicative (UpdateCT p s w) where
    pure = UpdateCT . pure . const . (, mempty)
    UpdateCT ff <*> UpdateCT fa = UpdateCT $ liftA2
        (\ff' fa' s ->
            let
              ~(f, p1)    = ff' s
              ~(a, p2)   =  fa' (act p1 s)
            in
              (f a, p1 <> p2)
        ) ff fa

instance (Semigroup p, Monoid p, Action p s) => Monad (Update p s) where
    m >>= f = update $ \s ->
        let
            ~(a, p1)    = runUpdate m s
            ~(b, p2)    = runUpdate (f a) (act p1 s)
        in
            (b, p1 <> p2)

instance (Semigroup s, Monoid s, Comonad w) => Comonad (UpdateCT p s w) where
    extract = fst . ($ mempty) . extract . runUpdateCT
    extend f = UpdateCT . extend (\wf s -> (f $ UpdateCT $ fmap (. (s <>)) wf, snd $ extract wf s)) . runUpdateCT

{-
Adapted version of the StateCT comonad proof.
This is a gigantic slog. If you want to see the simpler proof for a non-transformer version, scroll past to the next comment block.
Damn I wish I knew how to coq.

(UpdateCT s w) is a comonad.

extend extract = id
    extend f m = UpdateCT $ extend (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    extend extract m = UpdateCT $ extend (\wf s -> (extract (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (extract (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) . extract . runUpdateCT $ (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) . extract $ fmap (. (s <>)) wf), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract . fmap (. (s <>))) wf), snd $ extract wf s)) (runUpdateCT m)
        -- extract . fmap f = f . extract
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) $ ((. (s <>)) . extract) wf), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract wf) (. (s <>)), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst . ($ mempty) $ (extract wf . (s <>)), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst $ extract wf (s <> mempty), snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> (fst $ extract wf s, snd $ extract wf s)) (runUpdateCT m)
    = UpdateCT $ extend (\wf s -> extract wf s) (runUpdateCT m)
    = UpdateCT $ extend extract (runUpdateCT m)
    = UpdateCT $ runUpdateCT m
    = m

extract . extend f = f
    extend f m = UpdateCT $ extend (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    extract (extend f m) = fst . ($ mempty) . extract . runUpdateCT $ UpdateCT $ extend (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    = fst . ($ mempty) . extract $ extend (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    = fst . ($ mempty) $ (extract . extend (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s))) (runUpdateCT m)
        -- extract . extend f = f
    = fst . ($ mempty) $ (\wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)) (runUpdateCT m)
    = fst . ($ mempty) $ (\s -> (f (UpdateCT (fmap (. (s <>)) (runUpdateCT m))), snd $ extract (runUpdateCT m) s))
    = fst $ (f (UpdateCT (fmap (. (mempty <>)) (runUpdateCT m))), snd $ extract (runUpdateCT m) mempty)
    = f (UpdateCT (fmap (. (mempty <>)) (runUpdateCT m)))
    = f (UpdateCT (fmap (. id) (runUpdateCT m)))
    = f (UpdateCT (fmap id (runUpdateCT m)))
    = f (UpdateCT (runUpdateCT m))
    = f m

extend f . extend g = extend (f . extend g)
    let help fun = \wf s -> (f (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)

    extend f (extend g m) = UpdateCT $ extend (help f) (runUpdateCT (UpdateCT $ extend (help g) (runUpdateCT m)))
            -- runUpdateCT . UpdateCT = id
        = UpdateCT $ extend (help f) (extend (help g) (runUpdateCT m))
        = UpdateCT $ (extend (help f) . extend (help g)) (runUpdateCT m)
            -- extend f . extend g = extend (f . extend g)
        = UpdateCT $ (extend (help f . extend (help g))) (runUpdateCT m)
            -- expansion
        = UpdateCT $ extend (\wf s -> help f (extend (help g) wf) s) (runUpdateCT m)

        -- we'll now study subexpression

        (\wf s -> help f (extend (help g) wf) s)
        = \wf s -> (f (UpdateCT (fmap (. (s <>)) (extend (help g) wf))), snd $ extract (extend (help g) wf) s)
        = \wf s -> (..., snd $ extract (extend (help g) wf) s)
            -- extract . extend f = f
        = \wf s -> (..., snd $ (help g) wf s)
        = \wf s -> (..., snd $ (\wf' s' -> (..., snd $ extract wf' s')) wf s)
        = \wf s -> (..., snd $ (..., snd $ extract wf s))
        = \wf s -> (..., snd $ extract wf s)
        = \wf s -> (f (UpdateCT (fmap (. (s <>)) (extend (help g) wf))), ...)
            -- fmap f = extend (f . extract)
        = \wf s -> (f (UpdateCT (extend ((. (s <>)) . extract) (extend (help g) wf))), ...)
            -- extend f . extend g = extend (f . extend g)
        = \wf s -> (f (UpdateCT (extend ((. (s <>)) . extract . extend (help g)) wf)), ...)
            -- extract . extend f = f
        = \wf s -> (f (UpdateCT (extend ((. (s <>)) . help g) wf)), ...)

        -- we'll now study subexpression
        (. (s <>)) . help g
        = \wf' -> help g wf' . (s <>)
        = \wf' s' -> help g wf' (s <> s')

        -- thus
        (\wf s -> help f (extend (help g) wf) s)
        = \wf s -> (f (UpdateCT (extend ((. (s <>)) . help g) wf)), ...)
        = \wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), ...)
        = \wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)

        --thus
        extend f (extend g m)
        = UpdateCT $ extend (\wf s -> help f (extend (help g) wf) s) (runUpdateCT m)
        = UpdateCT $ extend (\wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)) (runUpdateCT m)


    extend (f . extend g) m = UpdateCT $ extend (help (f . extend g)) (runUpdateCT m)
            -- expand definition of extend
        = UpdateCT $ extend (help (f . UpdateCT . extend (help g) . runUpdateCT)) (runUpdateCT m)
            -- expansion
        = UpdateCT $ extend (\wf s -> help (f . UpdateCT . extend (help g) . runUpdateCT) wf s) (runUpdateCT m)

        -- we'll now study subexpression
        (\wf s -> help (f . UpdateCT . extend (help g) . runUpdateCT) wf s)
            -- expand definition of help
        = \wf s -> ((f . UpdateCT . extend (help g) . runUpdateCT) (UpdateCT (fmap (. (s <>)) wf)), snd $ extract wf s)
            -- runUpdateCT . UpdateCT = id
        = \wf s -> ((f . UpdateCT . extend (help g) . fmap (. (s <>))) wf, snd $ extract wf s)
            -- because
            -- fmap f = extend (f . extract)
            -- and
            -- extend f . extend g = extend (f . extend g)
            -- therefore
            -- extend f . fmap g = extend (f . fmap g)
        = \wf s -> ((f . UpdateCT . extend (help g . fmap (. (s <>)))) wf, ...)
            -- apply wf
        = \wf s -> (f (UpdateCT (extend (help g . fmap (. (s <>))) wf)), ...)

        -- we'll now study subexpression
        help g . fmap (. (s <>))
            -- expand
        = \wf' s' -> help g (fmap (. (s <>)) wf') s'
            -- expand definition of help
        = \wf' s' -> (f (UpdateCT (fmap (. (s' <>)) (fmap (. (s <>)) wf'))), snd $ extract (fmap (. (s <>)) wf') s')
        = \wf' s' -> (..., snd $ extract (fmap (. (s <>)) wf') s')
            -- extract . fmap f = f . extract
        = \wf' s' -> (..., snd $ (. (s <>)) (extract wf') s')
        = \wf' s' -> (..., snd $ (extract wf' . (s <>)) s')
        = \wf' s' -> (..., snd $ extract wf' (s <> s'))
        = \wf' s' -> (f (UpdateCT (fmap (. (s' <>)) (fmap (. (s <>)) wf'))), ...)
            -- fmap f . fmap g = fmap (f . g)
        = \wf' s' -> (f (UpdateCT (fmap ((. (s' <>)) . (. (s <>))) wf')), ...)

        -- we'll now study subexpression
        (. (s' <>)) . (. (s <>))
            -- expand
        = \st -> (. (s' <>)) ((. (s <>)) st)
            -- apply
        = \st -> st . (s <>) . (s' <>)
            -- expand
        = \st s'' -> st (s <> (s' <> s''))
        = \st s'' -> st (s <> s' <> s'')
            -- make point-free
        = \st -> st . (<> s <> s'))
        = (. (<> s <> s'))

        -- thus
        help g . fmap (. (s <>))
        = \wf' s' -> (g (UpdateCT (fmap ((. (<> s')) . (. (s <>))) wf')), ...)
        = \wf' s' -> (g (UpdateCT (fmap (. (<> s <> s')) wf')), ...)
        = \wf' s' -> (g (UpdateCT (fmap (. (<> s <> s')) wf')), snd $ extract wf' (s <> s'))
            -- collapse this to a use of help
        = \wf' s' -> help g wf' (s <> s')

        -- thus
        (\wf s -> help (f . UpdateCT . extend (help g) . runUpdateCT) wf s)
        = \wf s -> (f (UpdateCT (extend (help g . fmap (. (s <>))) wf)), ...)
        = \wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), ...)
        = \wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)

        -- thus
        extend (f . extend g) m
        = UpdateCT $ extend (\wf s -> help (f . UpdateCT . extend (help g) . runUpdateCT) wf s) (runUpdateCT m)
        = UpdateCT $ extend (\wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)) (runUpdateCT m)


    extend f (extend g m)
        = UpdateCT $ extend (\wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)) (runUpdateCT m)

    extend (f . extend g) m
        = UpdateCT $ extend (\wf s -> (f (UpdateCT (extend (\wf' s' -> help g wf' (s <> s')) wf)), snd $ extract wf s)) (runUpdateCT m)

    extend f . extend g = extend (f . extend g)
-}





{-
A slightly more digestible proof for a non-transformer version:

    newtype Update p s a = Update { runUpdate :: s -> (p, a) } deriving (Functor)

instance (Semigroup s, Monoid s) => Comonad (Update p s) where
    extract = snd . ($ mempty) . runUpdate
    extend f m = Update $ \s1 -> (fst $ runUpdate m s1, f (Update $ \s2 -> runUpdate m (s1 <> s2)))

    Proof that Update is a comonad when s is a monoid:

extend extract      = id
    extend extract m = Update $ \s1 -> (fst $ runUpdate m s1, extract (Update $ \s2 -> runUpdate m (s1 <> s2)))
        -- expanding definition of extract
        = Update $ \s1 -> (... , snd . ($ mempty) . runUpdate (Update $ \s2 -> runUpdate m (s1 <> s2)))
        = Update $ \s1 -> (... , snd . ($ mempty) . (\s2 -> runUpdate m (s1 <> s2)))
        = Update $ \s1 -> (... , snd $ runUpdate m (s1 <> mempty))
        = Update $ \s1 -> (fst $ runUpdate m s1 , snd $ runUpdate m s1)
        = Update $ \s1 -> runUpdate m s1
        = Update $ runUpdate m
        = m

extract . extend f  = f
    extract (extend f m) = extract $ Update $ \s1 -> (fst $ runUpdate m s1, f (Update $ \s2 -> runUpdate m (s1 <> s2)))
        -- expanding definition of extract
        = snd . ($ mempty) . runUpdate $ Update $ \s1 -> (fst $ runUpdate m s1, f (Update $ \s2 -> runUpdate m (s1 <> s2)))
        = snd . ($ mempty) $ \s1 -> (fst $ runUpdate m s1, f (Update $ \s2 -> runUpdate m (s1 <> s2)))
        = snd $ (fst $ runUpdate m mempty, f (Update $ \s2 -> runUpdate m (mempty <> s2)))
        = f (Update $ \s2 -> runUpdate m (mempty <> s2))
        = f (Update $ \s2 -> runUpdate m s2)
        = f (Update $ runUpdate m)
        = f m

extend f . extend g = extend (f . extend g)
    extend f (extend g m) = Update $ \s1 -> (fst $ runUpdate (extend g m) s1, f (Update $ \s2 -> runUpdate (extend g m) (s1 <> s2)))
        = Update $ \s1 -> (fst $ runUpdate (extend g m) s1, ...)
            -- expanding definitition of extend
        = Update $ \s1 -> (fst $ runUpdate (Update $ \s2 -> (fst $ runUpdate m s2, ...) s1, ...)
        = Update $ \s1 -> (fst $ (fst $ runUpdate m s1, ...), ...)
        = Update $ \s1 -> (fst $ runUpdate m s1, ...)
        = Update $ \s1 -> (..., f (Update $ \s2 -> runUpdate (extend g m) (s1 <> s2)))
            -- expanding definition of extend, and applying runUpdate
        = Update $ \s1 ->
            (
                ...,
                f (Update $ \s2 -> (fst $ runUpdate m (s1 <> s2), g (Update $ \s3 -> runUpdate m ((s1 <> s2) <> s3))))
            )

        = Update $ \s1 ->
            (
                fst $ runUpdate m s1,
                f $ Update $ \s2 ->
                    (
                        fst $ runUpdate m (s1 <> s2),
                        g (Update $ \s3 -> runUpdate m (s1 <> s2 <> s3))
                    )
            )

        extend (f . extend g) m = Update $ \s1 -> (fst $ runUpdate m s1, f . extend g $ Update $ \s2 -> runUpdate m (s1 <> s2))
        = Update $ \s1 ->
            (
                ...,
                f . extend g $ Update $ \s2 ->
                    runUpdate m (s1 <> s2)
            )
            --extending definition of extend g
        = Update $ \s1 ->
            (
                ...,
                f $ Update $ \s3 ->
                    (
                        fst $ runUpdate (Update $ \s2 -> runUpdate m (s1 <> s2)) s3,
                        g $ Update $ \s4 -> runUpdate (Update $ \s2 -> runUpdate m (s1 <> s2)) (s3 <> s4)
                    )
            )
            -- apply the runUpdates we can
        = Update $ \s1 ->
            (
                ...,
                f $ Update $ \s3 ->
                    (
                        fst $ runUpdate m (s1 <> s3),
                        g $ Update $ \s4 -> runUpdate m (s1 <> (s3 <> s4))
                    )
            )
            -- simplify, and rename s3 to s2; rename s4 to s3

        = Update $ \s1 ->
            (
                fst $ runUpdate m s1,
                f $ Update $ \s2 ->
                    (
                        fst $ runUpdate m (s1 <> s2),
                        g $ Update $ \s3 -> runUpdate m (s1 <> s2 <> s3)
                    )
            )

    so
        extend f . extend g = extend (f . extend g)

    Update is a comonad, given that s is a monoid.

-}

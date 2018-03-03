{-# LANGUAGE TupleSections, GADTs, DeriveFunctor, FlexibleInstances, DefaultSignatures, FunctionalDependencies, ScopedTypeVariables, UndecidableInstances #-}
module Control.Comonad.Update where

-- The update comonad transformer.
-- "UpdateCT p s w" is a comonad as long as s is a monoid (and w is a comonad).

import Data.Monoid.Action
import Data.Monoid.Reaction
import Data.Semigroup
import Control.Comonad
import Control.Monad.Identity
import Control.Applicative

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
{-
    I'll need to prove this... Non-transformer version is proven.

    If I change "fst . sap $ s1 <> s2" to "fst . sap $ s2 <> s1", then the Reaction laws would change such that Reaction s p would become identical to Action s (s -> p)
    That would be somewhat confusing though. For one, the default instance of Reaction would become:
    react s1 f s2 = f (s2 <> s1)
-}
instance (Semigroup s, Monoid s, Reaction s p, Comonad w) => Comonad (UpdateCT p s w) where
    extract = fst . ($ mempty) . extract . runUpdateCT
    extend f = UpdateCT . extend (\wf s1 -> (f . UpdateCT $ fmap (\sap s2 -> (fst . sap $ s1 <> s2, react' s1 s2 (snd . sap))) wf, snd $ extract wf s1)) . runUpdateCT


{-
newtype Update s p a = Update { runUpdate :: s -> (a, p) } deriving (Functor)
instance (Semigroup s, Monoid s, Reaction s p) => Comonad (Update s p) where
    extract = fst . ($ mempty) . runUpdate
    extend f m = Update $ \s1 ->
      (
          f . Update $ \s2 ->
              (
                  fst . runUpdate m $ s1 <> s2,
                  react' s1 s2 (snd . runUpdate m)
              )
        , snd $ runUpdate m s1
      )

Proof that Update is a Comonad.

    extend extract === id
        extend extract m = Update $ \s1 -> (extract . Update $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), snd $ runUpdate m s1)
            = Update $ \s1 -> (fst . ($ mempty) . runUpdate . Update $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), snd $ runUpdate m s1)
            = Update $ \s1 -> (fst . ($ mempty) $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), snd $ runUpdate m s1)
            = Update $ \s1 -> (fst (fst . runUpdate m $ s1 <> mempty, ...), snd $ runUpdate m s1)
            = Update $ \s1 -> (fst . runUpdate m $ s1 <> mempty, snd $ runUpdate m s1)
            = Update $ \s1 -> (fst $ runUpdate m s1, snd $ runUpdate m s1)
            = Update $ \s1 -> runUpdate m s1
            = m

    extract . extend f === f
        extract (extend f) m = extract $ Update $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), ...)
            = fst . ($ mempty) . runUpdate $ Update $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), ...)
            = fst . ($ mempty) $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate m $ s1 <> s2, ...), ...)
            = fst $ (f . Update $ \s2 -> (fst . runUpdate m $ mempty <> s2, ...), ...)
            = f . Update $ \s2 -> (fst . runUpdate m $ mempty <> s2, ...)
            = f . Update $ \s2 -> (fst $ runUpdate m s2, react' mempty s2 (snd . runUpdate m))
                -- Coaction law
            = f . Update $ \s2 -> (fst $ runUpdate m s2, (snd . runUpdate m) s2)
            = f . Update $ \s2 -> (fst $ runUpdate m s2, snd $ runUpdate m s2)
            = f . Update $ \s2 -> runUpdate m s2
            = f m


    extend f (extend g m) === extend (f . extend g) m
        extend f (extend g m) = Update $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate (extend g m) $ s1 <> s2, react' s1 s2 (snd . runUpdate (extend g m))), snd $ runUpdate (extend g m) s1)
            = Update $ \s1 -> (..., snd $ runUpdate (extend g m) s1)
            = Update $ \s1 -> (..., snd $ runUpdate (Update $ \s1' -> (..., runUpdate $ m s1')) s1)
            = Update $ \s1 -> (..., snd $ (..., runUpdate $ m s1))
            = Update $ \s1 -> (..., runUpdate $ m s1)
            = Update $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate (extend g m) $ s1 <> s2, ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (fst . runUpdate (Update $ \s' -> (g . Update $ \s3 -> (fst . runUpdate m $ s' <> s3, react' s' s3 (snd . runUpdate m)))) $ s1 <> s2, ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (fst $ (g . Update $ \s3 -> (fst . runUpdate m $ s1 <> s2 <> s3, ...)), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . runUpdate m $ s1 <> s2 <> s3, react' (s1 <> s2) s3 (snd . runUpdate m)), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., react' s1 s2 (snd . runUpdate (extend g m))), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., react' s1 s2 (snd . runUpdate (Update $ \s' -> (..., snd $ runUpdate m s')))), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., react' s1 s2 (snd . (\s' -> (..., snd $ runUpdate m s')))), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., react' s1 s2 (snd . runUpdate m)), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., ...), snd $ runUpdate (extend g m) s1)
                -- snd . runUpdate (extend g m) === snd . runUpdate m
            = Update $ \s1 -> (f . Update $ \s2 -> (..., ...), snd $ runUpdate m s1)
            = Update $ \s1 ->
              (
                f . Update $ \s2 ->
                  (
                    g . Update $ \s3 ->
                      (
                        fst . runUpdate m $ s1 <> s2 <> s3
                      , react' (s1 <> s2) s3 (snd . runUpdate m)
                      )
                  , react' s1 s2 (snd . runUpdate m)
                  )
              , snd $ runUpdate m s1
              )

        extend (f . extend g) m = Update $ \s1 -> (f . extend g $ Update \s' -> (fst . runUpdate m $ s1 <> s', react' s1 s' (snd . runUpdate m)), snd $ runUpdate m s1)
            -- let inner = Update \s' -> (fst . runUpdate m $ s1 <> s', react' s1 s' (snd . runUpdate m))
            = Update $ \s1 -> (f . extend g $ inner, ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . runUpdate inner $ s2 <> s3, react' s2 s3 (snd . runUpdate inner)), snd $ runUpdate inner s2), snd $ runUpdate m s1)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., snd $ runUpdate inner s2), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., snd $ runUpdate (Update \s' -> (fst . runUpdate m $ s1 <> s', react' s1 s' (snd . runUpdate m))) s2), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., snd $ runUpdate (Update \s' -> (..., react' s1 s' (snd . runUpdate m))) s2), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., snd $ (..., react' s1 s2 (snd . runUpdate m))), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (..., react' s1 s2 (snd . runUpdate m)), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . runUpdate inner $ s2 <> s3, react' s2 s3 (snd . runUpdate inner)), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . runUpdate (Update $ \s' -> (fst . runUpdate m $ s1 <> s', react' s1 s' (snd . runUpdate m))) $ s2 <> s3, ...), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . (fst . runUpdate m $ s1 <> s2 <> s3, ...)), ...), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (fst . runUpdate m $ s1 <> s2 <> s3, ...), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (..., react' s2 s3 (snd . runUpdate inner)), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (..., react' s2 s3 (snd . runUpdate $ Update \s' -> (..., react' s1 s' (snd . runUpdate m)))), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (..., react' s2 s3 (snd . (\s' -> (..., react' s1 s' (snd . runUpdate m))))), ...), ...)
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (..., react' s2 s3 (\s' -> react' s1 s' (snd . runUpdate m))), ...), ...)
                -- Coaction law
            = Update $ \s1 -> (f . Update $ \s2 -> (g . Update $ \s3 -> (..., react' (s1 <> s2) s3 (snd . runUpdate m)), ...), ...)
            = Update $ \s1 ->
              (
                f . Update $ \s2 ->
                  (
                    g . Update $ \s3 ->
                      (
                        fst . runUpdate m $ s1 <> s2 <> s3
                      , react' (s1 <> s2) s3 (snd . runUpdate m)
                      )
                  , react' s1 s2 (snd . runUpdate m)
                  )
              , snd $ runUpdate m s1
              )

    extend f . extend g === extend (f . extend g)
-}

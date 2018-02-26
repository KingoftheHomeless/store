{-# LANGUAGE TupleSections, DeriveFunctor, FlexibleInstances, MultiParamTypeClasses #-}
module Control.Monad.Coupdate where

-- The Coupdate monad.
-- Makes use of the Coaction class I invented.

import Data.Semigroup
import Data.Monoid.Action
import Data.Monoid.Coaction
import Control.Comonad

-- I've had absolutely no luck finding a monad transformer of this.
data Coupdate s p a = Coupdate { peek :: s -> a, pos :: p } deriving (Functor)

-- It should be possible to make the Applicative/Monad instance of Coupdate be even more general. Perhaps by doing the following?
{-

class Action p s => Superaction s p where
    react :: p -> (s -> p) -> p

instance (Semigroup p, Monoid p, Superaction s p) => Applicative (Coupdate s p) where
    pure a = Coupdate (const a) mempty
    (<*>) = ap

instance (Semigroup p, Monoid p, Superaction s p) => Monad (Coupdate s p) where
    m >>= f = Coupdate
        (\s -> peek (f $ peek m s) $ act (pos m) s)
        (pos m <> react (pos m) (pos . f . peek m))

-- This would allow you to encode the update monad in the Coupdate monad, through the following:

newtype Reader s p = Reader { runReader :: s -> p }

type Update s p a = Coupdate s (Reader s p)

instance Semigroup p => Semigroup (Reader s p) where
    a <> b = Reader $ \s -> runReader a s <> runReader b s

instance Action p s => Action (Reader s p) s where
    act f s = act (runReader f s) s

instance Action p s => Superaction s (Reader s p) where
    react a f = Reader $ \s -> runReader (f s) $ act a s

-- Question is, what laws could there be for Superaction to guarantee that Coupdate is a monad, if possible at all.
-}

instance (Semigroup p, Monoid p) => Applicative (Coupdate s p) where
    pure a = Coupdate (const a) mempty
    Coupdate sf p1 <*> Coupdate sa p2 = Coupdate (\s -> sf s $ sa s) (p1 <> p2)     -- TODO: check (<*>) = ap

instance (Semigroup p, Monoid p, Coaction s p) => Monad (Coupdate s p) where
    m >>= f = Coupdate
        (\s -> peek (f $ peek m s) s)
        (pos m <> reflect (pos . f . peek m))

instance (Monoid s, Action s p) => Comonad (Coupdate s p) where
    extract (Coupdate wf _) = wf mempty
    extend k (Coupdate wf p) = Coupdate (\s -> k $ Coupdate wf (act s p)) p

{-
PROOF that Coupdate is a Monad:

I will be using the following definition of join in my proof:
join m = Coupdate
    (\s -> peek (peek m s) s)
    (pos m <> reflect (pos . peek m))


join . pure = id
    join (pure m) = join $ Coupdate (const m) mempty
        -- expanding definition of join
        = Coupdate (\s -> peek (peek (Coupdate (const m) mempty) s) s) (...)

        = Coupdate (\s -> peek ((const m) s) s) (...)
        = Coupdate (\s -> peek m s) (...)
        = Coupdate (peek m) (...)
        = Coupdate (...) (pos (Coupdate (const m) mempty) <> reflect (pos . peek (Coupdate (const m) mempty)))
        = Coupdate (...) (mempty <> reflect (pos . const m))
        = Coupdate (...) (mempty <> reflect (\_ -> pos m))
            -- Coaction law
        = Coupdate (...) (mempty <> pos m)
        = Coupdate (...) (pos m)
        = Coupdate (peek m) (pos m)
        = m

join . fmap pure = id
    join (fmap pure m) = join $ Coupdate (pure . peek m) (pos m)
        -- expanding definition of join
        = Coupdate (\s -> peek (peek (Coupdate (pure . peek m) (pos m)) s) s) (...)
        = Coupdate (\s -> peek ((pure . peek m) s) s) (...)
        = Coupdate (\s -> peek (Coupdate (const $ peek m s) mempty) s) (...)
        = Coupdate (\s -> (const $ peek m s) s) (...)
        = Coupdate (\s -> peek m s) (...)
        = Coupdate (peek m) (...)
        = Coupdate (..) (pos (Coupdate (pure . peek m) (pos m)) <> reflect (pos . peek (Coupdate (pure . peek m) (pos m))))
        = Coupdate (..) (pos m <> reflect (pos . pure . peek m))
        = Coupdate (..) (pos m <> reflect (\s -> pos $ Coupdate (const $ peek m s) mempty))
        = Coupdate (..) (pos m <> reflect (\_ -> mempty))
            -- Coaction law
        = Coupdate (..) (pos m <> mempty)
        = Coupdate (..) (pos m)
        = Coupdate (peek m) (pos m)
        = m


join . join = join . fmap join
    join (join m) = Coupdate (\s -> peek (peek (join m) s) s) (pos (join m) <> reflect (pos . peek (join m)))
        = Coupdate (\s -> peek (peek (join m) s) s) (...)
        = Coupdate (\s -> peek (peek (Coupdate (\s' -> peek (peek m s') s') (...)) s) s) (...)
        = Coupdate (\s -> peek (\s' -> peek (peek m s') s') s) s) (...)
        = Coupdate (\s -> peek (peek (peek m s) s) s) (...)
        = Coupdate (\s -> peek (peek (peek m s) s) s) (...)
        = Coupdate (...) (pos (join m) <> reflect (pos . peek (join m)))
        = Coupdate (...) (pos (join m) <> (...))
        = Coupdate (...) (pos (Coupdate (\s -> peek (peek m s) s) (pos m <> reflect (pos . peek m))) <> (...))
        = Coupdate (...) (pos m <> reflect (pos . peek m) <> (...))
        = Coupdate (...) ((...) <> reflect (pos . peek (join m)))
        = Coupdate (...) ((...) <> reflect (pos . peek (Coupdate (\s -> peek (peek m s) s) (...))))
        = Coupdate (...) ((...) <> reflect (pos . (\s -> peek (peek m s) s)))
        = Coupdate (...) ((...) <> reflect (\s' -> pos $ (\s -> peek (peek m s) s) s'))
        = Coupdate (...) ((...) <> reflect (\s' -> pos $ peek (peek m s') s'))
        = Coupdate
            (\s -> peek (peek (peek m s) s) s)
            (pos m <> reflect (pos . peek m) <> reflect (\s' -> pos $ peek (peek m s') s'))


    join (fmap join m) = Coupdate (\s -> peek (peek (fmap join m) s) s) (pos (fmap join m) <> reflect (pos . peek (fmap join m)))
        = Coupdate (\s -> peek (peek (fmap join m) s) s) (...)
        = Coupdate (\s -> peek (peek (Coupdate (join . peek m) (pos m)) s) s) (...)
        = Coupdate (\s -> peek ((join . peek m) s) s) (...)
        = Coupdate (\s -> peek ((\s' -> join (peek m s')) s) s) (...)
        = Coupdate (\s -> peek (join (peek m s)) s) (...)
        = Coupdate (\s -> peek (Coupdate (\s' -> peek (peek (peek m s') s') s') (...)) s) (...)
        = Coupdate (\s -> (\s' -> peek (peek (peek m s') s') s') s) (...)
        = Coupdate (\s -> peek (peek (peek m s) s) s) (...)
        = Coupdate (...) (pos (fmap join m) <> reflect (pos . peek (fmap join m)))
        = Coupdate (...) (pos (fmap join m) <> (...))
        = Coupdate (...) (pos (Coupdate (join . peek m) (pos m)) <> (...))
        = Coupdate (...) (pos m <> (...))
        = Coupdate (...) (pos m <> reflect (pos . peek (fmap join m)))
        = Coupdate (...) (pos m <> reflect (\s' -> pos $ peek (fmap join m) s'))
        = Coupdate (...) (pos m <> reflect (\s' -> pos $ peek (Coupdate (join . peek m) (pos m)) s'))
        = Coupdate (...) (pos m <> reflect (\s' -> pos $ (join . peek m) s'))
        = Coupdate (...) (pos m <> reflect (\s' -> pos $ join $ peek m s'))
        = Coupdate (...) (pos m <> reflect (\s' -> pos $ Coupdate (...) (pos (peek m s') <> reflect (pos . peek (peek m s')))))
        = Coupdate (...) (pos m <> reflect (\s' -> pos (peek m s') <> reflect (pos . peek (peek m s'))))
            -- let f = pos . peek m
            -- let g = (pos .) . peek . peek m
            -- let g' = reflect . g
        = Coupdate (...) (pos m <> reflect (\s' -> f s' <> g' s'))
            -- Coaction law
        = Coupdate (...) (pos m <> reflect f <> reflect g')
        = Coupdate (...) (pos m <> reflect f <> reflect (reflect . g))
        = Coupdate (...) (pos m <> reflect f <> reflect (\s' -> reflect (g s')))
            -- Coaction law
        = Coupdate (...) (pos m <> reflect f <> reflect (\s' -> g s' s'))
        = Coupdate (...) (pos m <> reflect f <> reflect (\s' -> ((pos .) . peek . peek m) s' s'))
        = Coupdate (...) (pos m <> reflect f <> reflect (\s' -> (pos . peek (peek m s')) s'))
        = Coupdate (...) (pos m <> reflect f <> reflect (\s' -> pos $ peek (peek m s') s'))
        = Coupdate
            (\s -> peek (peek (peek m s) s) s)
            (pos m <> reflect f <> reflect (\s' -> pos $ peek (peek m s') s'))

    join . join = fmap join . join

-}

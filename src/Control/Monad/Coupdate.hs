{-# LANGUAGE TupleSections, DeriveFunctor #-}
module Control.Monad.Coupdate where

-- The Coupdate monad.
-- Makes use of the Coaction class I invented.

import Data.Semigroup
import Data.Monoid.Action
import Data.Monoid.Coaction
import Control.Comonad

-- I've had absolutely no luck finding a monad transformer of this.
data Coupdate p s a = Coupdate { peek :: s -> a, pos :: p } deriving (Functor)

instance (Semigroup p, Monoid p) => Applicative (Coupdate p s) where
    pure a = Coupdate (const a) mempty
    Coupdate sf p1 <*> Coupdate sa p2 = Coupdate (\s -> sf s $ sa s) (p1 <> p2)     -- TODO: check (<*>) = ap

instance (Semigroup p, Monoid p, Coaction p s) => Monad (Coupdate p s) where
    m >>= f = Coupdate
        (\s -> peek (f $ peek m s) s)
        (pos m <> reflect (pos . f . peek m))

instance (Monoid p, Action p s) => Comonad (Coupdate s p) where
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

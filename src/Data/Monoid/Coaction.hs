{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}
module Data.Monoid.Coaction where
{-

The Coaction class and its laws were tailor-made in order to make sure that Coupdate is a monad whem using them.
I don't intend to say, by any means, that Coaction is somehow the categorical dual of an Action. I simply chose the name because it was fitting.

-}

import Data.Coerce
import Data.Semigroup
import Data.Monoid.Action

{-
Instance selection should probably be driven by the second type parameter,
so that trivial instances wouldn't cause overlap.
Of course, I'm a bit of a hypocrite, and don't actually do that.
(Perhaps the order of the type parameters should be switched?)

    LAWS:
        reflect (const p) = p
        reflect (\s -> f s <> g s) = reflect f <> reflect g
        reflect (\s -> reflect (f s)) = reflect (\s -> f s s)
-}
class Coaction m s where
    reflect :: (m -> s) -> s

instance Coaction () s where
    reflect f = f ()

{-
There are an infinite amount of trivial Coaction instances.

imagine there exists the type class:

class Trivial m where
    trivial :: m

with the only law being that trivial is not a bottom.

If so, this instance follows the Coaction laws (proof at the end of this file).
instance Trivial m => Coaction m s where
    reflect = ($ trivial)

These trivial cases could actually be of use. For example:

instance Trivial (Maybe s) where
    trivial = Nothing

in this case,
Coupdate s (Maybe s) a
    ~   (Maybe s -> a, s)
    ~   (s -> a, a, s)
    ~   Product ((->) s) ((,) s) a

It will bind the same way, too.

Of course, a Trivial typeclass would cause too much overlap to actually exist.
It's better to use newtypes to create Coaction instances as needed.
-}

newtype MemptyCoactor s = MemptyCoactor { runMemptyCoactor:: s }

instance Semigroup s => Semigroup (MemptyCoactor s) where
    (<>) = coerce ((<>) :: s -> s -> s)

instance Monoid s => Monoid (MemptyCoactor s) where
    mempty  = coerce (mempty :: s)
    mappend = coerce (mappend :: s -> s -> s)

instance Monoid m => Coaction (MemptyCoactor m) l where
    reflect = ($ MemptyCoactor mempty)


-- Monoidic Reader
-- Its semigroup instance is liftA2 (<>) of the reader functor.
newtype MReader s a = MReader { runMReader :: s -> a }

instance Semigroup a => Semigroup (MReader s a) where
    MReader a <> MReader b = MReader $ \s -> a s <> b s

instance (Semigroup a, Monoid a) => Monoid (MReader s a) where
    mappend = (<>)
    mempty  = MReader (const mempty)


newtype ReaderActor s = ReaderActor { runReaderActor :: s }

instance Coaction (ReaderActor s) (MReader (ReaderActor s) a) where
    reflect f = MReader $ \s -> runMReader (f s) s

instance Coaction (ReaderActor s) (Endo (ReaderActor s)) where
    reflect f = Endo $ \s -> appEndo (f s) s

{-
MReader is a Coaction.

reflect (const p) = p
    reflect (const p) = MReader $ \s -> runMReader (const p s) s
    = MReader $ \s -> runMReader p s
    = MReader $ runMReader p
    = p

reflect (\s -> f s <> g s) = reflect f <> reflect g

    reflect (\s -> f s <> g s) = MReader $ \s -> runMReader ((\s' -> f s' <> g s') s) s
        = MReader $ \s -> runMReader (f s <> g s) s
            -- using Semigroup definition of MReader
        = MReader $ \s -> runMReader (MReader $ \s' -> runMReader (f s) s' <> runMReader (g s) s') s
        = MReader $ \s -> runMReader (f s) s <> runMReader (g s) s

    reflect f <> reflect g = MReader $ \s -> runMReader (reflect f) s <> runMReader (reflect g) s
        = MReader $ \s -> runMReader (MReader $ \s' -> runMReader (f s') s') s <> runMReader (MReader $ \s' -> runMReader (g s') s') s
        = MReader $ \s -> runMReader (f s) s <> runMReader (g s) s

reflect (\s -> reflect (f s)) = reflect (\s -> f s s)

    reflect (\s -> reflect (f s)) = MReader $ \s -> runMReader ((\s' -> reflect (f s')) s) s
    = MReader $ \s -> runMReader (reflect (f s)) s
    = MReader $ \s -> runMReader (MReader $ \s' -> runMReader (f s s') s') s
    = MReader $ \s -> runMReader (f s s) s
    = MReader $ \s -> runMReader ((\s' -> f s' s') s) s
    = reflect (\s -> f s s)

-}

instance (Semigroup p, Coaction s p) => Action (MReader s p) p where
    act f p = reflect (runMReader f) <> p

{-
Proof that this is an action:
If p is monoid, (MReader s p) is a monoid.

act mempty = id
    act mempty p = reflect (runMReader mempty) <> p
        -- using monoid instance of MReader
    = reflect (runMReader (MReader $ const mempty)) <> p
    = reflect (const mempty) <> p
        -- coaction law
    = mempty <> p
    = p

act (m1 <> m2) p = act m1 $ act m2 p
    act (m1 <> m2) p = reflect (runMReader (m1 <> m2)) p
        -- using semigroup instance of MReader
    = reflect (runMReader $ MReader $ \s -> runMReader m1 s <> runMReader m2 s) <> p
    = reflect (\s -> runMReader m1 s <> runMReader m2 s) <> p
        -- coaction law
    = reflect (runMReader m1) <> reflect (runMReader m2) <> p
    = reflect (runMReader m1) <> (reflect (runMReader m2) <> p)
        -- definition of act
    == act m1 $ act m2 p


Interestingly, this proof does not make use of the Coaction law that
reflect (\s -> (reflect f s)) = reflect (\s -> f s s)
Does that have any significance?
Perhaps one coaction law can be deduced from the others?

-- (s -> a, s -> p)

-}


{-
instance Trivial s => Coaction p s where
    reflect = ($ trivial)

is a Coaction.

reflect (const p) = p
    reflect (const p) = (const p) $ trivial
    = p

reflect (\s -> f s <> g s) = reflect f <> reflect g
    reflect (\s -> f s <> g s) = (\s -> f s <> g s) $ trivial
    = f trivial <> g trivial
    = ($ trivial) f <> ($ trivial) g
    = reflect f <> reflect g

reflect (\s -> reflect (f s)) = reflect (\s -> f s s)
    reflect (\s -> reflect (f s)) = (\s -> reflect (f s)) $ trivial
    = reflect (f trivial)
    = (f trivial trivial)
    = reflect (\s -> f s s)

-}

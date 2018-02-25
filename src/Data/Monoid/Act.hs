{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeOperators #-}
module Data.Monoid.Act where
{-
This module defines the oh-so-cleverly named Act,
which, based off a Monoid, may be used to create "embeddings"
of it, and the corresponding monoids/actions.
(And yes, I'm aware that these cause overlapping issues.)

    instance Semigroup s => Action s (Act p s)

    instance Semigroup p => Semigroup (Act s (Act s p))

    instance (Semigroup p, Monoid p) => Monoid (Act s (Act s p))

For example,
    () (Act p ())       ~ () (() -> p)
is an action (since () is a monoid)

Therefore,
    Act p (Act p ())    ~ (() -> p) -> p
is a monoid (Endo p)

Therefore,
    (Act p (Act p ())) (Act p (Act p (Act p ()))) ~ ((() -> p) -> p) (((() -> p) -> p) -> p) ~ (p -> p) ((p -> p) -> p)
is an action.

etc.

The instance
instance Semigroup p => Semigroup (Act p ())
also exists.

Act may also be used to create Coactions:
instance Coaction (Act p s) s

which may be used for the Coupdate monad if "Act p s" is a monoid, which it is if
    s ~ ()

    or

    (Monoid s', s ~ Act p s')

HOWEVER, I have not checked that the Coaction laws are actually followed in the latter case. I suspect that they are.
-}

import Data.Monoid.Action
import Data.Semigroup


import Data.Monoid.Coaction

newtype Act p s = Act { runAct :: s -> p }

infixr 1 <-:
type (<-:) = Act


-- Unfortunate overlap between this and the Action () l instance.
instance Semigroup s => Action s (Act p s) where
    act s1 (Act f) = Act $ \s2 -> f (s1 <> s2)


instance Semigroup p => Semigroup (Act p ()) where
    Act a <> Act b = Act $ const $ a () <> b ()

instance (Semigroup p, Monoid p) => Monoid (Act p ()) where
    mempty  = Act (const mempty)
    mappend = (<>)

instance Semigroup p => Semigroup (Act s (Act s p)) where
    Act ps's1 <> Act ps's2 = Act $ \ps -> ps's2 $ Act $ \p1 -> ps's1 $ act p1 ps

{-
Theres an
    

-}

instance (Semigroup p, Monoid p) => Monoid (Act s (Act s p)) where
    mempty  = Act $ \(Act f) -> f mempty
    mappend = (<>)

instance Coaction (Act p s) s where
    reflect f = Act $ \s -> runAct (f s) s

-- I don't actually know if this works. Probably not.
instance (Semigroup p, Coaction p s) => Action (Act p s) p where
    act f p = reflect (runAct f) <> p

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}
module Data.Monoid.Coaction where
{-

The Coaction class and its laws were tailor-made in order to make sure that Coupdate is a monad whem using them.
I don't intend to say, by any means, that Coaction is somehow the categorical dual of an Action. I simply chose the name because it was fitting.

I'm not sure if "(Monoid p, Coaction p s)" is not simply the same as saying (Monoid p, Monoid s).
I don't think so. Not if the "Coaction (Act p s) s" instance is legal.
(Monoid p, Monoid s) certainly implies Coaction p s, though.

LAWS:
    reflect (const p) = p
    reflect (\s -> f s <> g s) = reflect f <> reflect g
    reflect (\s -> reflect (g s)) = reflect (\s -> g s s)

-}

import Data.Coerce
import Data.Semigroup

class Coaction p s where
    reflect :: (s -> p) -> p

instance Coaction () l where
    reflect _ = ()

instance {-# OVERLAPPING #-} Coaction l () where
    reflect f = f ()

newtype EmptyReflect s = EmptyReflect { runEmptyReflect :: s }

instance Semigroup s => Semigroup (EmptyReflect s) where
    (<>) = coerce ((<>) :: s -> s -> s)

instance Monoid s => Monoid (EmptyReflect s) where
    mempty  = coerce (mempty :: s)
    mappend = coerce (mappend :: s -> s -> s)

instance Monoid s => Coaction l (EmptyReflect s) where
    reflect = ($ EmptyReflect mempty)

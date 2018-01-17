module Control.Comonad.Store.Trans where
import Control.Comonad
import Control.Comonad.Store

{-
    Can't do this with only a Monad constraint of m.
    It's possible to get the type signature to work, but it will
    inevitably break right and left identity.
    The reason is because a value of type (a) needs to be produced in order to build
    the stored value during binding. Thus, (peek ma mempty) needs to be bound to b,
    and then the stored value of b is mappended to the stored value of a.
    This requires the stored value to also be wrapped in the monad, which results in it
    gaining the effects of (f mempty) during binding.
    Thus, (a >>= pure) is not a, because whatever effects (peek a mempty) have are added
    to the stored value.
    I've only found two ways to circumvent this:
        newtype StoreT s m a = StoreT (m (s -> a, s))
            This isn't compatible with the (Store s a) we're interested in.
            The interesting properties would be lost.
        Completely separate the computations for storing the value and reading it
            This actually works out; but it's not unique. See Control.Monad.Prescient
-}

-- This is a complete spitball; I have no idea if this works or not.
instance (Monoid s, Applicative m, Comonad m) => Monad (StoreT s m) where
    StoreT f s1 >>= b =
        StoreT
            (fmap (\f' s -> peek s . b $ f' s) f)
            (mappend s1 . pos . b $ extract f mempty)

module Control.Monad.Warp where
import Control.Monad.Co
import Control.Comonad
import Data.Functor.Yoneda
import Control.Monad.State

{-

Co (State s) a  ~ forall r. (s -> (a -> r, s)) -> r
                ~ forall r. (s -> a -> r, s -> s) -> r
                ~ forall r. (s -> a -> r) -> (s -> s) -> r
                ~ forall r. ((s, a) -> r) -> (s -> s) -> r
                ~ Yoneda ((->) (s -> s)) (s, a)
                ~ (s -> s) -> (s, a)

However, it binds differently from (ReaderT (s -> s) ((,) s) a)

-}

-- This is an Update monad. s is a monoid that acts upon the monoid (Endo s).
newtype Warp s a = Warp { runWarp :: (s -> s) -> (s, a) }

runWarp' :: Warp s a -> (s, a)
runWarp' = (`runWarp` id)


instance Functor (Warp s) where
    fmap f (Warp f') = Warp (fmap f . f')

{-
    Probable Applicative/Monoid instances. Haven't checked if any laws hold;
    Simply inspected if these instances produces identical results
    in my experiments compared to using Co (State s). So far, I haven't found
    anything wrong with these.
-}
instance Monoid s => Applicative (Warp s) where
    pure a = Warp $ const (mempty, a)
    ff <*> fa = Warp $ \ss ->
        let
            (s1, f) = runWarp ff ss
            (s2, a) = runWarp fa (ss . mappend s1)
        in
            (mappend s1 s2, f a)

instance Monoid s => Monad (Warp s) where
    ma >>= mb = Warp $ \ss ->
        let
            (s1, a) = runWarp ma ss
            (s2, b) = runWarp (mb a) (ss . mappend s1)
        in
            (mappend s1 s2, b)

-- Clumsy isomorphic transformations derived from my proof
toWarp :: Co (State s) a -> Warp s a
toWarp m = Warp $ lowerYoneda $ Yoneda $ \sar ss -> (runCo m . state) . mend $ (curry sar, ss)
    where
        mend :: (a -> b, a -> c) -> a -> (b, c)
        mend (f, g) a = (f a, g a)

fromWarp :: Warp s a -> Co (State s) a
fromWarp (Warp m) = co $ \st -> uncurry (runYoneda (liftYoneda m)) ((\(f, a) -> (uncurry f, a)) . split $ runState st)
    where
        split :: (a -> (b, c)) -> (a -> b, a -> c)
        split f = (fst . f, snd . f)

-- Similar to the Comonad for State.
instance Comonad (Warp s) where
    extract m = snd $ runWarp m id
    duplicate m = Warp $ \ss1 -> (fst $ runWarp m ss1, Warp $ \ss2 -> runWarp m $ ss2 . ss1)
{-
Proof that (Warp s) is a comonad:

extract . duplicate == id
    duplicate m = Warp $ \ss1 -> (fst $ runWarp m ss1, Warp $ \ss2 -> runWarp m $ ss2 . ss1)
    extract (duplicate m) = snd $ runWarp (duplicate m) id
    = snd $ (fst $ runWarp m id, Warp $ \ss2 -> runWarp m $ ss2 . id)
    = Warp $ \ss2 -> runWarp m $ ss2 . id
    = Warp $ \ss2 -> runWarp m ss2
    = m

fmap extract . duplicate == id
    duplicate m = Warp $ \ss1 -> (fst $ runWarp m ss1, Warp $ \ss2 -> runWarp m $ ss2 . ss1)
    fmap extract (duplicate m) = Warp $ \ss1 -> (fst $ m ss1, extract $ Warp $ \ss2 -> m $ ss2 . ss1)
    = Warp $ \ss1 -> (fst $ m ss1, snd $ runWarp (Warp $ \ss2 -> m $ ss2 . ss1) id)
    = Warp $ \ss1 -> (fst $ m ss1, snd $ m $ id . ss1)
    = Warp $ \ss1 -> (fst $ m ss1, snd $ m ss1)
    = Warp $ \ss1 -> m ss1
    = m

-- Sorry about the confusing variable names. This is not as tidy as I would have liked.
duplicate . duplicate = fmap duplicate . duplicate
    duplicate . duplicate = 
        duplicate m = Warp $ \ss1 -> (fst $ runWarp m ss1, Warp $ \ss2 -> runWarp m (ss2 . ss1))
        duplicate (duplicate m) = Warp $ \ss3 -> (fst $ runWarp (duplicate m) ss3, Warp $ \ss4 -> runWarp (duplicate m) (ss4 . ss3))
        = Warp $ \ss3 -> (fst $ runWarp (Warp \ss1 -> (fst $ runWarp m ss1, ...)) ss3, ... )
        = Warp $ \ss3 -> (fst $ (fst $ runWarp m ss3, ...), ... )
        = Warp $ \ss3 -> (fst $ runWarp m ss3, ...)
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> runWarp (duplicate m) (ss4 . ss3))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> runWarp (\ss1 -> (fst $ runWarp m ss1, Warp $ \ss2 -> runWarp m (ss2 . ss1))) (ss4 . ss3))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . (ss4 . ss3))))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))
        = Warp $ \ss3 -> (fst $ runWarp m ss3, Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))

    fmap duplicate . duplicate =
        -- Renamed variables to make the later quality more clear
        duplicate m = Warp $ \ss3 -> (fst $ runWarp m ss3, Warp $ \ss1 -> runWarp m $ ss1 . ss3)
        fmap duplicate (duplicate m) = Warp $ \ss3 -> (fst $ runWarp m ss3, duplicate $ Warp $ \ss1 -> runWarp m (ss1 . ss3))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (fst $ runWarp (Warp $ \ss1 -> runWarp m (ss1 . ss3)) ss4, Warp $ \ss2 -> runWarp (Warp $ \ss1 -> runWarp m $ ss1 . ss3) (ss2 . ss4)))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (fst $ runWarp (Warp $ \ss1 -> runWarp m (ss1 . ss3)) ss4, ...))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), ...))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (..., Warp $ \ss2 -> runWarp (Warp $ \ss1 -> runWarp m $ ss1 . ss3) (ss2 . ss4)))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (..., Warp $ \ss2 -> runWarp m ((ss2 . ss4) . ss3)))
        = Warp $ \ss3 -> (..., Warp $ \ss4 -> (..., Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))
        = Warp $ \ss3 -> (fst $ runWarp m ss3, Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))

    duplicate . duplicate $ m =
        = Warp $ \ss3 -> (fst $ runWarp m ss3, Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))

    fmap duplicate . duplicate $ m =
        = Warp $ \ss3 -> (fst $ runWarp m ss3, Warp $ \ss4 -> (fst $ runWarp m (ss4 . ss3), Warp $ \ss2 -> runWarp m (ss2 . ss4 . ss3)))
        
    duplicate . duplicate = fmap duplicate . duplicate

-}

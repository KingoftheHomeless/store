{-# LANGUAGE FunctionalDependencies, FlexibleInstances, FlexibleContexts, DefaultSignatures, TupleSections, RankNTypes #-}
module Main where
import Control.Monad.Trans
import Control.Monad.Prescient
import Control.Monad.State
-- import Control.Monad.Warp
import Control.WarpFamily
import Control.Comonad.Update
import Control.Monad.Coupdate
import Data.Monoid.Action
import Data.Monoid.Coaction
import Data.Monoid.Act

experimental :: (MonadIO m, MonadStR Bool m) => m String
experimental = do
    written <- getWriting
    result  <- getReading
    when (maybe False not written) (replace True)
    case result of
        Just x  | x         -> liftIO (putStrLn "All is fine.") >> return "good"
                | otherwise -> liftIO (putStrLn "Somebody hates us!") >> return "bad"
        _                   -> liftIO (putStrLn "reading") >> return "reading"

-- example :: Co (State [Bool]) String
-- example = fromWarp $ Warp $ \ss -> if length (ss mempty) < 10 then (ss [True, True, True, True], "goood") else (mempty, "bad")

-- example2 :: String -> Co (State [Bool]) Bool
-- example2 str = fromWarp $ Warp $ \ss -> if str == "goood" then (ss $ replicate 6 False, True) else (replicate 10 False, False)

main :: IO ()
main = pure ()



-- data WStoreT s m a = WStoreT { peek :: s -> Codensity m a,
--                                pos :: Codensity m s }
-- -- forall r. (a -> m r) -> s -> m r
-- -- (b -> r)
-- -- forall r. (s -> m r) -> a -> m r
-- runWStoreT :: Monad m => WStoreT s m a -> m a
-- runWStoreT (WStoreT rd wr) = lowerCodensity (wr >>= rd)

-- instance Monoid s => Functor (WStoreT s m) where
--     fmap = liftM

-- instance Monoid s => Applicative (WStoreT s m) where
--     pure = return
--     (<*>) = ap

-- instance Monoid s => Monad (WStoreT s m) where
--     return a = WStoreT (const (pure a)) (pure mempty)
--     WStoreT rd wr >>= f =
--       WStoreT
--         (\s -> rd s >>= ($ s) . peek . f)
--         (Codensity $ \smr -> runCodensity wr $ \s -> runCodensity (rd s) $ \a -> runCodensity (pos $ f a) smr)
--         -- (Codensity $ \smr -> runCodensity wr $ \s1 -> runCodensity (rd mempty) $ \a -> runCodensity (pos $ f a) $ \s2 -> smr $ s1 <> s2)

-- instance Monoid s => MonadTrans (WStoreT s) where
--     lift m = WStoreT (const (lift m)) (pure mempty)

-- instance (MonadIO m, Monoid s) => MonadIO (WStoreT s m) where
--     liftIO = lift . liftIO

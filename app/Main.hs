{-# LANGUAGE FunctionalDependencies, FlexibleInstances, FlexibleContexts, DefaultSignatures, TupleSections, RankNTypes #-}
module Main where
import Data.Monoid
import Data.IORef
import Control.Monad.Trans
import Control.Monad.Prescient
import Control.Monad.State
import Control.Comonad.State
import Control.Monad.Warp
import Control.Monad.Co

experimental :: (MonadIO m, MonadStR Bool m) => m String
experimental = do
    written <- getWriting
    result  <- getReading
    when (maybe False not written) (replace True)
    case result of
        Just x  | x         -> liftIO (putStrLn "All is fine.") >> return "good"
                | otherwise -> liftIO (putStrLn "Somebody hates us!") >> return "bad"
        _                   -> liftIO (putStrLn "reading") >> return "reading"

example :: Co (State [Bool]) String
example = fromWarp $ Warp $ \ss -> if length (ss mempty) < 10 then (ss [True, True, True, True], "goood") else (mempty, "bad")

example2 :: String -> Co (State [Bool]) Bool
example2 str = fromWarp $ Warp $ \ss -> if str == "goood" then (ss $ replicate 6 False, True) else (replicate 10 False, False)

main :: IO ()
main = pure ()
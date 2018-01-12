{-# LANGUAGE FunctionalDependencies, FlexibleInstances, FlexibleContexts, DefaultSignatures, TupleSections, RankNTypes #-}
module Main where
import Control.Monad.Store.Class
import Data.Monoid

testing :: (Monad m, MonadStore (Sum Int) m) => [a] -> m String
testing start = do
    write $ Sum . length $ start
    (Sum now) <- scry
    if now >= 5 then
        return $ replicate now 'b'
    else do
        write 1
        return $ replicate now 'a'

ex :: MonadStore (Sum Int) m => m String
ex = store (flip replicate 'c' . getSum) 9

hmst :: (MonadStore (Sum Int) m, Enum a) => [a] -> m [Int]
hmst s = store (\(Sum now) -> map fromEnum (take now s)) mempty

main :: IO ()
main = pure ()
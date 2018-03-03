{-# LANGUAGE FlexibleInstances, DefaultSignatures, MultiParamTypeClasses, ScopedTypeVariables #-}
module Data.Monoid.Reaction where

import Data.Semigroup
import Data.Monoid.Action
import Data.Monoid.MList
import Data.Coerce

{-
Reaction s p is the same as "Action (Dual s) (s -> p)"
Instance resolution should be determined by the first argument.

LAWS:
    react mempty = id
    react (s1 <> s2) = react s2 . react s1

Expressed in terms of react':
    react' mempty s2 f = f s2
    react' (s1 <> s2) s3 f = react' s2 s3 (\s' -> react' s1 s' f)


Maybe s -> (Maybe s -> p) -> (Maybe s -> p)

Maybe s -> (s -> p, p) -> (s -> p, p)


-}
class Reaction s p where
    react :: s -> (s -> p) -> s -> p
    default react :: Semigroup s => s -> (s -> p) -> s -> p
    react s1 f s2 = f (s1 <> s2)
    {-# INLINE react #-}

react' :: Reaction s p => s -> s -> (s -> p) -> p
react' = flip . react
{-# INLINE react' #-}

instance Action s p => Reaction (Dual s) p where
    react (Dual s) = (act s .)
    {-# INLINE react #-}

-- TODO: Make a less evil instance.
instance Reaction s p => Action (Dual s) (s -> p) where
    act = coerce (react :: s -> (s -> p) -> s -> p )
    {-# INLINE act #-}

instance Reaction s p => Reaction (Maybe s) p where
    react (Just s1) f = maybe (f Nothing) (react s1 (f . Just))
    react _         f = f
    {-# INLINE react #-}

instance Reaction (SM a) () where
    react _ _ _ = ()
    {-# INLINE react #-}

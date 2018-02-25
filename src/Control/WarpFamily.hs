{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
module Control.WarpFamily where

-- The Warp family, formed by chaining "Act"s
-- As these are both monads and comonads, I didn't really know where to put them.

import Data.Monoid.Act
import Control.Comonad
import Control.Comonad.Update
import Control.Monad.Coupdate

data Prog    = Succ Prog | Unit

type Zero   = 'Unit
type One    = 'Succ Zero
type Two    = 'Succ One
type Three  = 'Succ Two
type Four   = 'Succ Three
type Five   = 'Succ Four
type Six    = 'Succ Five
type Seven  = 'Succ Six
type Eight  = 'Succ Seven
type Nine   = 'Succ Eight

type family WarpLvl (n :: Prog) s where
    WarpLvl 'Unit s     = ()
    WarpLvl ('Succ n) s = s <-: WarpLvl n s

type Warper (n :: Prog) s   = Update (WarpLvl n s) (WarpLvl ('Succ n) s)

type Cowarper (n :: Prog) s = Coupdate (WarpLvl ('Succ n) s) (WarpLvl n s)

-- Isomorphic to (s -> a)
-- Always a monad. Comonad when s is a monoid.
type Warp0 s = Warper Zero s

-- Isomorphic to (s -> s) -> (s, a)
-- Monad when s is a monoid. Always a comonad.
type Warp1 s = Warper One s

warp1M :: Warp1 [Bool] String
warp1M = return "warp1"

warp1C :: String
warp1C = extract warp1M

-- This is Co (Warp1 s)
-- Isomorphic to ((s -> s) -> s) -> (s -> s, a)
-- Always a monad. Comonad when s is a monoid.
type Warp2 s = Warper Two s

warp2M :: Warp2 [Bool] String
warp2M = return "warp2"

warp2C :: String
warp2C = extract warp2M

-- This is Co (Warp2 s)
-- Isomorphic to (((s -> s) -> s) -> s) -> ((s -> s) -> s, a)
-- Monad when s is a monoid. Always a comonad.
type Warp3 s = Warper Three s

warp3M :: Warp3 [Bool] String
warp3M = return "warp3"

warp3C :: String
warp3C = extract warp3M



-- Isomorphic to (s, a)
-- Monad when s is a monoid. Always a comonad.
type Cowarp0 s = Cowarper Zero s

-- Isomorphic to s -> (s, a)
-- Binds differently from State.
-- Always a monad. Comonad when s is a monoid.
type Cowarp1 s = Cowarper One s

-- Isomorphic to Warp1. Binds differently from it.
-- Monad when s is a monoid. Always a comonad.
type Cowarp2 s = Cowarper Two s

-- Isomorphic to Warp2. Binds differently from it.
-- Always a monad. Comonad when s is a monoid.
type Cowarp3 s = Cowarper Three s

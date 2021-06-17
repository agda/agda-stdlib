------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Clock simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module System.Clock.Primitive where

open import Agda.Builtin.Nat using (Nat)
open import IO.Primitive using (IO)
open import Foreign.Haskell using (Pair)

data Clock : Set where
  Monotonic RealTime ProcessCPUTime : Clock
  ThreadCPUTime MonotonicRaw BootTime : Clock
  MonotonicCoarse RealTimeCoarse : Clock

{-# COMPILE GHC Clock = data Clock (Monotonic | Realtime | ProcessCPUTime
                                   | ThreadCPUTime | MonotonicRaw | Boottime
                                   | MonotonicCoarse | RealtimeCoarse )
#-}

postulate getTime : Clock → IO (Pair Nat Nat)

{-# FOREIGN GHC import System.Clock  #-}
{-# FOREIGN GHC import Data.Function #-}
{-# COMPILE GHC getTime = fmap (\ (TimeSpec a b) -> ((,) `on` fromIntegral) a b) . getTime #-}

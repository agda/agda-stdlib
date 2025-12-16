------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Clock simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module System.Clock.Primitive where

open import Agda.Builtin.Nat using (Nat)
open import IO.Primitive.Core using (IO)
open import Foreign.Haskell using (Pair)

data Clock : Set where
  monotonic realTime processCPUTime : Clock
  threadCPUTime monotonicRaw : Clock

{-# FOREIGN GHC import System.Clock  #-}

{-# FOREIGN GHC
data AgdaClock
  = AgdaMonotonic
  | AgdaRealTime
  | AgdaProcessCPUTime
  | AgdaThreadCPUTime
  | AgdaMonotonicRaw

fromAgdaClock :: AgdaClock -> Clock
fromAgdaClock ac = case ac of
  AgdaMonotonic -> Monotonic
  AgdaRealTime -> RealTime
  AgdaProcessCPUTime -> ProcessCPUTime
  AgdaThreadCPUTime -> ThreadCPUTime
  AgdaMonotonicRaw -> MonotonicRaw
#-}

{-# COMPILE GHC Clock =
  data AgdaClock
  ( AgdaMonotonic
  | AgdaRealtime
  | AgdaProcessCPUTime
  | AgdaThreadCPUTime
  | AgdaMonotonicRaw
  )
#-}

postulate getTime : Clock → IO (Pair Nat Nat)

{-# FOREIGN GHC import Data.Function #-}
{-# COMPILE GHC getTime = fmap (\ (TimeSpec a b) -> ((,) `on` fromIntegral) a b) . getTime . fromAgdaClock #-}

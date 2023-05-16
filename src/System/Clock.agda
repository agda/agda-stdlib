------------------------------------------------------------------------
-- The Agda standard library
--
-- Measuring time
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.Clock where

open import Level using (Level; 0ℓ; Lift; lower)
open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _∸_; _^_; _<ᵇ_)
import Data.Nat.Show as ℕ
open import Data.Nat.DivMod using (_/_)
import Data.Nat.Properties as ℕₚ
open import Data.String.Base using (String; _++_; padLeft)

open import IO.Base
open import Function.Base using (_$_; _∘′_)
open import Foreign.Haskell using (_,_)

open import Relation.Nullary.Decidable using (False; fromWitnessFalse; toWitnessFalse)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Re-exporting the Clock data structure

open import System.Clock.Primitive as Prim
  public
  using ( Clock
        -- System-wide monotonic time since an arbitrary point in the past
        ; monotonic
        -- System-wide real time since the Epoch
        ; realTime
        -- Amount of execution time of the current process
        ; processCPUTime
        -- Amount of execution time of the current OS thread
        ; threadCPUTime
        -- A raw hardware version of Monotonic ignoring adjustments
        ; monotonicRaw
        -- Linux-specific clocks
        -- Similar to Monotonic, includes time spent suspended
        ; bootTime
        -- Faster but less precise alternative to Monotonic
        ; monotonicCoarse
        -- Faster but less precise alternative to RealTime
        ; realTimeCoarse
        )

------------------------------------------------------------------------
-- Defining a more convenient representation

record Time : Set where
  constructor mkTime
  field seconds     : ℕ
        nanoseconds : ℕ
open Time public

------------------------------------------------------------------------
-- Reading the clock

getTime : Clock → IO Time
getTime c = do
  (a , b) ← lift (Prim.getTime c)
  pure $ mkTime a b

------------------------------------------------------------------------
-- Measuring time periods

diff : Time → Time → Time
diff (mkTime ss sns) (mkTime es ens) =
  if ens <ᵇ sns
  then mkTime (es ∸ suc ss) ((1000000000 + ens) ∸ sns)
  else mkTime (es ∸ ss) (ens ∸ sns)

record Timed (A : Set a) : Set a where
  constructor mkTimed
  field value : A
        time  : Time

time : IO A → IO (Timed A)
time io = do
  start ← lift! $ getTime realTime
  a     ← io
  end   ← lift! $ getTime realTime
  pure $ mkTimed a $ diff (lower start) (lower end)

time′ : IO {0ℓ} A → IO Time
time′ io = Timed.time <$> time io

------------------------------------------------------------------------
-- Showing time

show : Time →   -- Time in seconds and nanoseconds
       Fin 10 → -- Number of decimals to show
                -- (in [0,9] because we are using nanoseconds)
       String
show (mkTime s ns) prec = secs ++ "s" ++ padLeft '0' decimals nsecs where
  decimals = toℕ prec
  secs     = ℕ.show s
  prf      = ℕₚ.m^n≢0 10 (9 ∸ decimals)
  nsecs    = ℕ.show ((ns / (10 ^ (9 ∸ decimals))) {{prf}})

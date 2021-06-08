------------------------------------------------------------------------
-- The Agda standard library
--
-- Measuring time
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module System.Clock where

open import Level using (Level; 0ℓ; Lift; lower)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _^_; _<ᵇ_)
open import IO.Base
open import Function.Base using (_$_; _∘′_)
open import Foreign.Haskell using (_,_)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Re-exporting the Clock data structure

open import System.Clock.Primitive as Prim
  using ( Clock
        ; Monotonic
        ; Realtime
        ; ProcessCPUTime
        ; ThreadCPUTime
        ; MonotonicRaw
        ; Boottime
        ; MonotonicCoarse
        ; RealtimeCoarse
        )
  public

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
  return $ mkTime a b

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
  start ← lift! $ getTime Realtime
  a     ← io
  end   ← lift! $ getTime Realtime
  return $ mkTimed a $ diff (lower start) (lower end)

time′ : IO {0ℓ} A → IO Time
time′ io = Timed.time <$> time io

------------------------------------------------------------------------
-- Showing time

import Data.Nat.Show as ℕ
open import Data.Nat.DivMod using (_div_)
import Data.Nat.Properties as ℕₚ
open import Data.Fin.Base using (Fin; toℕ)
open import Data.String.Base using (String; _++_; padLeft)
open import Data.Char.Base using (Char)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse; toWitnessFalse)

show : Time → Fin 9 → String
show (mkTime s ns) prec = secs ++ "s" ++ padLeft '0' decimals nsecs where
  decimals  = toℕ prec
  secs      = ℕ.show s
  nsecs     = ℕ.show ((ns div (10 ^ (9 ∸ decimals)))
                           {exp-nz 10 (9 ∸ decimals)})

   where

    exp-nz : ∀ x n {x≠0 : False (x ℕₚ.≟ 0)} → False (x ^ n ℕₚ.≟ 0)
    exp-nz x n {x≠0} = fromWitnessFalse (toWitnessFalse x≠0 ∘′ ℕₚ.m^n≡0⇒m≡0 x n)

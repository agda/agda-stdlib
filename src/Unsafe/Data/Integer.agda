------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on integers
------------------------------------------------------------------------

module Unsafe.Data.Integer where

open import Data.Integer public

open import Data.Sign as Sign using (Sign)
import Unsafe.Data.Nat.Show as ℕ
open import Data.String.Base using (String ; _++_)

------------------------------------------------------------------------
-- Conversions

-- Decimal string representation.

show : ℤ → String
show i = showSign (sign i) ++ ℕ.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.- = "-"
  showSign Sign.+ = ""

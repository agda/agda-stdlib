-----------------------------------------------------------------------
-- The Agda standard library
--
-- Example showing the use of the partiality Monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module README.Effect.Monad.Partiality where

open import Codata.Musical.Notation using (♯_)
open import Data.Bool.Base using (false; true)
open import Data.Nat using (ℕ; _+_; _∸_; _≤?_)
open import Effect.Monad.Partiality
open import Relation.Nullary.Decidable using (does)

open Workaround

-- McCarthy's f91:

f91′ : ℕ → ℕ ⊥P
f91′ n with does (n ≤? 100)
... | true  = later (♯ (f91′ (11 + n) >>= f91′))
... | false = now (n ∸ 10)

f91 : ℕ → ℕ ⊥
f91 n = ⟦ f91′ n ⟧P

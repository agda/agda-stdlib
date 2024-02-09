------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded where

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Nat.Bounded.Base public

------------------------------------------------------------------------
-- Publicly re-export properties

open import Data.Nat.Bounded.Properties public
  using
  -- queries
  (
   _≟_
  -- equalities
  ; ⟦⟧≡⟦⟧⇒≡ ; ≡⇒⟦⟧≡⟦⟧
  ; ≡-mod⇒fromℕ≡fromℕ ; fromℕ≡fromℕ⇒≡-mod
  -- inversions
  ; _/∼≡fromℕ ; _/∼≡fromℕ⁻¹; /∼≡-injective
  )

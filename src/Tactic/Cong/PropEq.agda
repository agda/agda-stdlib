------------------------------------------------------------------------
-- The Agda standard library
--
-- Tactic.Cong specialised to use Propositional Equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat
open import Level
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
import Tactic.Cong

module Tactic.Cong.PropEq
  (recursion-limit : ℕ)
  (Param : Setω)
  (Family-Level : Param → Level)
  (Family : (A : Param) → Set (Family-Level A))
  (_<_ : ∀ {A : Param} → Family A → Family A → Set (Family-Level A))
  (≡-<-trans : ∀ {A : Param} → Trans {A = Family A} {B = Family A} {C = Family A} _≡_ _<_ _<_)
  where

open Tactic.Cong 0 _≡_ cong Param Family-Level Family _<_ ≡-<-trans renaming (_≈⌊_⌋_ to _≡⌊_⌋_) public

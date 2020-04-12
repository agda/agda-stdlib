--------------------------------------------------------------------------------
-- The Agda standard library
--
-- Tactic.Cong.PropEq specialised to operate over the family of all types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
import Tactic.Cong.PropEq
open import Tactic.Cong.Common

module Tactic.Cong.PropEq.ForAllTypes
  (recursion-limit : ℕ)
  (_<_ : ∀ {a} {A : Set a} → A → A → Set a)
  (≡-<-trans : ∀ {a} {A : Set a} → Trans {A = A} {B = A} {C = A} _≡_ _<_ _<_)
  where

open Tactic.Cong.PropEq 0 ℓSet projₗ projₛ _<_ ≡-<-trans public

------------------------------------------------------------------------
-- The Agda standard library
--
-- Concepts from rewriting theory
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.Rewriting where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; ∃ ; _,_)
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.ReflexiveTransitive


Det : ∀ {a b ℓ₁ ℓ₂} → {A : Set a} → {B : Set b} → Rel B ℓ₁ → REL A B ℓ₂ → Set _
Det _≈_ _—→_ = ∀ {x y z} → x —→ y → x —→ z → y ≈ z

Deterministic : ∀ {a b ℓ} → {A : Set a} → {B : Set b} → REL A B ℓ → Set _
Deterministic = Det _≡_

Confluent : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Confluent _—→_ = ∀ {A B C} → (A —↠ B × A —↠ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
     _—↠_ = Star _—→_

Diamond : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Diamond _—→_ = ∀ {A B C} → (A —→ B × A —→ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
    _—↠_ = Star _—→_

det⟶conf : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → Deterministic r → Confluent r
det⟶conf f (ε , snd) = _ , snd , ε
det⟶conf f (a ◅ fst , ε) = _ , ε , a ◅ fst
det⟶conf f (a ◅ fst , b ◅ snd) rewrite f a b = det⟶conf f ( fst , snd )

conf⟶diamond : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → Confluent r → Diamond r
conf⟶diamond c (fst , snd) = c (fst ◅ ε , snd ◅ ε)

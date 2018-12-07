------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of constructions over unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Properties where

open import Data.Product using (_×_; _,_; swap; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.Core hiding (Decidable)
open import Relation.Unary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (¬?)
open import Function using (_$_; _∘_)

----------------------------------------------------------------------
-- The empty set

module _ {a} {A : Set a} where

  ∅? : Decidable {A = A} ∅
  ∅? _ = no λ()

  ∅-Empty : Empty {A = A} ∅
  ∅-Empty x ()

  ∁∅-Universal : Universal {A = A} (∁ ∅)
  ∁∅-Universal = λ x x∈∅ → x∈∅

----------------------------------------------------------------------
-- The universe

module _ {a} {A : Set a} where

  U? : Decidable {A = A} U
  U? _ = yes tt

  U-Universal : Universal {A = A} U
  U-Universal = λ _ → _

  ∁U-Empty : Empty {A = A} (∁ U)
  ∁U-Empty = λ x x∈∁U → x∈∁U _

----------------------------------------------------------------------
-- Subset properties

module _ {a ℓ} {A : Set a} where

  ∅-⊆ : (P : Pred A ℓ) → ∅ ⊆ P
  ∅-⊆ P ()

  ⊆-U : (P : Pred A ℓ) → P ⊆ U
  ⊆-U P _ = _

  ⊆-refl : Reflexive (_⊆_ {A = A} {ℓ})
  ⊆-refl x∈P = x∈P

  ⊆-trans : Transitive (_⊆_ {A = A} {ℓ})
  ⊆-trans P⊆Q Q⊆R x∈P = Q⊆R (P⊆Q x∈P)

  ⊂-asym : Asymmetric (_⊂_ {A = A} {ℓ})
  ⊂-asym (_ , Q⊈P) = Q⊈P ∘ proj₁

----------------------------------------------------------------------
-- Decidability properties

module _ {a} {A : Set a} where

  ∁? : ∀ {ℓ} {P : Pred A ℓ} → Decidable P → Decidable (∁ P)
  ∁? P? x = ¬? (P? x)

  _∪?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
         Decidable P → Decidable Q → Decidable (P ∪ Q)
  _∪?_ P? Q? x = (P? x) ⊎-dec (Q? x)

  _∩?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
         Decidable P → Decidable Q → Decidable (P ∩ Q)
  _∩?_ P? Q? x = (P? x) ×-dec (Q? x)

module _ {a b} {A : Set a} {B : Set b} where

  _×?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred B ℓ₂} →
         Decidable P → Decidable Q → Decidable (P ⟨×⟩ Q)
  _×?_ P? Q? (a , b) = (P? a) ×-dec (Q? b)

  _⊙?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred B ℓ₂} →
         Decidable P → Decidable Q → Decidable (P ⟨⊙⟩ Q)
  _⊙?_ P? Q? (a , b) = (P? a) ⊎-dec (Q? b)

  _⊎?_ : ∀ {ℓ} {P : Pred A ℓ} {Q : Pred B ℓ} →
         Decidable P → Decidable Q → Decidable (P ⟨⊎⟩ Q)
  _⊎?_ P? Q? (inj₁ a) = P? a
  _⊎?_ P? Q? (inj₂ b) = Q? b

  _~? : ∀ {ℓ} {P : Pred (A × B) ℓ} →
        Decidable P → Decidable (P ~)
  _~? P? = P? ∘ swap

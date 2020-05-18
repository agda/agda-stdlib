------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Algebra where

open import Algebra
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Data.Product.Properties
open import Data.Unit using (⊤; tt)
open import Function.Base using (id; _∘′_; _∘_)
open import Level

open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Definitions as FuncDef

open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence)

------------------------------------------------------------------------

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b

-- The module is needed because we need to pass `A` and `B` to `FuncDef`
module _ {A : Set a} {B : Set b} where
  open FuncDef {A = A} {B} _≡_ _≡_

  -- mk↔ is a bit of a pain to use because here f and f⁻¹ need to always
  -- be specified.
  inverse : (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B
  inverse f f⁻¹ left right = mk↔ {f = f} {f⁻¹} (left , right)

private
  -- convenient abbreviations
  irefl : {A : Set a} {B : Set b} {f : A → B} (x : A) → f x ≡ f x
  irefl _ = refl

------------------------------------------------------------------------
-- Properties of ×

-- × is associative

×-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _×_
×-assoc ℓ _ _ _ = inverse assocʳ′ assocˡ′ irefl irefl

-- × is commutative.
-- We don't use Commutative because it isn't polymorphic enough.

×-comm : (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊤ is both left and right identity for ×
×-identityˡ : ∀ ℓ → LeftIdentity _↔_ (Lift ℓ ⊤) _×_
×-identityˡ _ _ = inverse proj₂ (lift tt ,_) irefl irefl

×-identityʳ : ∀ ℓ → RightIdentity _↔_ (Lift ℓ ⊤) _×_
×-identityʳ _ _ = inverse proj₁ (_, lift tt) irefl irefl

×-identity : ∀ ℓ → Identity _↔_ (Lift ℓ ⊤) _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- × has ⊥ has its zero

×-zeroˡ : ∀ ℓ → LeftZero _↔_ (Lift ℓ ⊥) _×_
×-zeroˡ ℓ A = inverse proj₁ (⊥-elim ∘ lower) (⊥-elim ∘ lower) (⊥-elim ∘ lower ∘ proj₁)

×-zeroʳ : ∀ ℓ → RightZero _↔_ (Lift ℓ ⊥) _×_
×-zeroʳ ℓ A = inverse proj₂ (⊥-elim ∘ lower) (⊥-elim ∘ lower) (⊥-elim ∘ lower ∘ proj₂)

×-zero : ∀ ℓ → Zero _↔_ (Lift ℓ ⊥) _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

------------------------------------------------------------------------
-- Properties of Σ

-- Σ is associative
Σ-assoc : {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = inverse assocʳ assocˡ irefl irefl

-- Σ is associative, alternate formulation
Σ-assoc-alt : {B : A → Set b} {C : Σ A B → Set c} →
          Σ (Σ A B) C ↔ Σ A (λ a → Σ (B a) (curry C a))
Σ-assoc-alt = inverse assocʳ-alt assocˡ-alt irefl irefl

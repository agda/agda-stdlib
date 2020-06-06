------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Algebra where

open import Algebra
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product
open import Data.Product.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘′_; _∘_)
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Level using (Level)

open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Definitions as FuncDef

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence; cong₂)

------------------------------------------------------------------------

private
  variable
    a b c d ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

-- The module is needed because we need to pass `A` and `B` to `FuncDef`
module _ {A : Set a} {B : Set b} where
  open FuncDef {A = A} {B} _≡_ _≡_

  -- mk↔ is a bit of a pain to use because here f and f⁻¹ need to always
  -- be specified.
  inverse : (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B
  inverse f f⁻¹ left right = mk↔ {f = f} {f⁻¹} (left , right)

private
  -- convenient abbreviations
  irefl : {f : A → B} (x : A) → f x ≡ f x
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
×-identityˡ : ∀ ℓ → LeftIdentity _↔_ (⊤ {ℓ}) _×_
×-identityˡ _ _ = inverse proj₂ (tt ,_) irefl irefl

×-identityʳ : ∀ ℓ → RightIdentity _↔_ (⊤ {ℓ}) _×_
×-identityʳ _ _ = inverse proj₁ (_, tt) irefl irefl

×-identity : ∀ ℓ → Identity _↔_ (⊤) _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- × has ⊥ has its zero

×-zeroˡ : ∀ ℓ → LeftZero _↔_ (⊥ {ℓ}) _×_
×-zeroˡ ℓ A = inverse proj₁ ⊥-elim ⊥-elim λ ()

×-zeroʳ : ∀ ℓ → RightZero _↔_ (⊥ {ℓ}) _×_
×-zeroʳ ℓ A = inverse proj₂ ⊥-elim ⊥-elim λ ()

×-zero : ∀ ℓ → Zero _↔_ (⊥) _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

-- × is a congruence
infix 4 _×-cong_

_×-cong_ : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
i ×-cong j = inverse (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  (λ {(a , b) → cong₂ _,_ (I.inverseˡ a) (J.inverseˡ b) })
  λ {(a , b) → cong₂ _,_ (I.inverseʳ a) (J.inverseʳ b)}
  where module I = Inverse i
        module J = Inverse j

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

------------------------------------------------------------------------
-- ⊤, _×_ form a commutative monoid

×-isMagma : ∀ ℓ → IsMagma {Level.suc ℓ} _↔_ _×_
×-isMagma ℓ = record
  { isEquivalence = ↔-isEquivalence
  ; ∙-cong        = _×-cong_
  }

×-magma : (ℓ : Level) → Magma _ _
×-magma ℓ = record
  { isMagma = ×-isMagma ℓ
  }

×-isSemigroup : ∀ ℓ → IsSemigroup {Level.suc ℓ} _↔_ _×_
×-isSemigroup ℓ = record
  { isMagma = ×-isMagma ℓ
  ; assoc   = λ _ _ _ → Σ-assoc
  }

×-semigroup : (ℓ : Level) → Semigroup _ _
×-semigroup ℓ = record
  { isSemigroup = ×-isSemigroup ℓ
  }

×-isMonoid : ∀ ℓ → IsMonoid _↔_ _×_ ⊤
×-isMonoid ℓ = record
  { isSemigroup = ×-isSemigroup ℓ
  ; identity    = (×-identityˡ ℓ) , (×-identityʳ ℓ)
  }

×-monoid : (ℓ : Level) → Monoid _ _
×-monoid ℓ = record
  { isMonoid = ×-isMonoid ℓ
  }

×-isCommutativeMonoid : ∀ ℓ → IsCommutativeMonoid _↔_ _×_ ⊤
×-isCommutativeMonoid ℓ = record
  { isMonoid = ×-isMonoid ℓ
  ; comm     = λ _ _ → ×-comm _ _
  }

×-commutativeMonoid : (ℓ : Level) → CommutativeMonoid _ _
×-commutativeMonoid ℓ = record
  { isCommutativeMonoid = ×-isCommutativeMonoid ℓ
  }

------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Algebra where

open import Algebra.Bundles
  using (Magma; Semigroup; Monoid; CommutativeMonoid; CommutativeSemiring)
open import Algebra.Definitions
open import Algebra.Structures
  using (IsMagma; IsSemigroup; IsMonoid; IsCommutativeMonoid
        ; IsSemiringWithoutAnnihilatingZero; IsSemiring; IsCommutativeSemiring)
open import Data.Bool.Base using (true; false)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product.Base
open import Data.Product.Properties
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Algebra using (⊎-isCommutativeMonoid)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (_∘′_)
open import Function.Bundles using (_↔_; Inverse; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong′; cong₂)

import Function.Definitions as FuncDef

------------------------------------------------------------------------

private
  variable
    a b c d p : Level
    A B C D : Set a

------------------------------------------------------------------------
-- Properties of Σ

-- Σ is associative
Σ-assoc : {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = mk↔ₛ′ assocʳ assocˡ cong′ cong′

-- Σ is associative, alternate formulation
Σ-assoc-alt : {B : A → Set b} {C : Σ A B → Set c} →
          Σ (Σ A B) C ↔ Σ A (λ a → Σ (B a) (curry C a))
Σ-assoc-alt = mk↔ₛ′ assocʳ-curried assocˡ-curried cong′ cong′

------------------------------------------------------------------------
-- Algebraic properties

-- × is a congruence
×-cong : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
×-cong i j = mk↔ₛ′ (map I.to J.to) (map I.from J.from)
  (λ {(a , b) → cong₂ _,_ (I.strictlyInverseˡ a) (J.strictlyInverseˡ b)})
  (λ {(a , b) → cong₂ _,_ (I.strictlyInverseʳ a) (J.strictlyInverseʳ b)})
  where module I = Inverse i; module J = Inverse j

-- × is commutative.
-- (we don't use Commutative because it isn't polymorphic enough)
×-comm : (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = mk↔ₛ′ swap swap swap-involutive swap-involutive

module _ (ℓ : Level) where

  -- × is associative
  ×-assoc : Associative {ℓ = ℓ} _↔_ _×_
  ×-assoc _ _ _ = mk↔ₛ′ assocʳ′ assocˡ′ cong′ cong′

  -- ⊤ is the identity for ×
  ×-identityˡ : LeftIdentity {ℓ = ℓ} _↔_ ⊤ _×_
  ×-identityˡ _ = mk↔ₛ′ proj₂ (tt ,_) cong′ cong′

  ×-identityʳ : RightIdentity {ℓ = ℓ} _↔_ ⊤ _×_
  ×-identityʳ _ = mk↔ₛ′ proj₁ (_, tt) cong′ cong′

  ×-identity : Identity _↔_ ⊤ _×_
  ×-identity = ×-identityˡ , ×-identityʳ

  -- ⊥ is the zero for ×
  ×-zeroˡ : LeftZero {ℓ = ℓ} _↔_ ⊥ _×_
  ×-zeroˡ A = mk↔ₛ′ proj₁ ⊥-elim ⊥-elim λ ()

  ×-zeroʳ : RightZero {ℓ = ℓ} _↔_ ⊥ _×_
  ×-zeroʳ A = mk↔ₛ′ proj₂ ⊥-elim ⊥-elim λ ()

  ×-zero : Zero _↔_ ⊥ _×_
  ×-zero = ×-zeroˡ , ×-zeroʳ

  -- × distributes over ⊎
  ×-distribˡ-⊎ : _DistributesOverˡ_ {ℓ = ℓ} _↔_ _×_ _⊎_
  ×-distribˡ-⊎ _ _ _ = mk↔ₛ′
    (uncurry λ x → [ inj₁ ∘′ (x ,_) , inj₂ ∘′ (x ,_) ]′)
    [ map₂ inj₁ , map₂ inj₂ ]′
    Sum.[ cong′ , cong′ ]
    (uncurry λ _ → Sum.[ cong′ , cong′ ])

  ×-distribʳ-⊎ : _DistributesOverʳ_ {ℓ = ℓ} _↔_ _×_ _⊎_
  ×-distribʳ-⊎ _ _ _ = mk↔ₛ′
    (uncurry [ curry inj₁ , curry inj₂ ]′)
    [ map₁ inj₁ , map₁ inj₂ ]′
    Sum.[ cong′ , cong′ ]
    (uncurry Sum.[ (λ _ → cong′) , (λ _ → cong′) ])

  ×-distrib-⊎ : _DistributesOver_ {ℓ = ℓ} _↔_ _×_ _⊎_
  ×-distrib-⊎ = ×-distribˡ-⊎ , ×-distribʳ-⊎

------------------------------------------------------------------------
-- Algebraic structures

  ×-isMagma : IsMagma {ℓ = ℓ} _↔_ _×_
  ×-isMagma = record
    { isEquivalence = ↔-isEquivalence
    ; ∙-cong        = ×-cong
    }

  ×-isSemigroup : IsSemigroup _↔_ _×_
  ×-isSemigroup = record
    { isMagma = ×-isMagma
    ; assoc   = λ _ _ _ → Σ-assoc
    }

  ×-isMonoid : IsMonoid _↔_ _×_ ⊤
  ×-isMonoid = record
    { isSemigroup = ×-isSemigroup
    ; identity    = ×-identityˡ , ×-identityʳ
    }

  ×-isCommutativeMonoid : IsCommutativeMonoid _↔_ _×_ ⊤
  ×-isCommutativeMonoid = record
    { isMonoid = ×-isMonoid
    ; comm     = ×-comm
    }

  ⊎-×-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _↔_ _⊎_ _×_ ⊥ ⊤
  ⊎-×-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ⊎-isCommutativeMonoid ℓ
    ; *-cong                = ×-cong
    ; *-assoc               = ×-assoc
    ; *-identity            = ×-identity
    ; distrib               = ×-distrib-⊎
    }

  ⊎-×-isSemiring : IsSemiring _↔_ _⊎_ _×_ ⊥ ⊤
  ⊎-×-isSemiring = record
    { isSemiringWithoutAnnihilatingZero = ⊎-×-isSemiringWithoutAnnihilatingZero
    ; zero                              = ×-zero
    }

  ⊎-×-isCommutativeSemiring : IsCommutativeSemiring _↔_ _⊎_ _×_ ⊥ ⊤
  ⊎-×-isCommutativeSemiring = record
    { isSemiring = ⊎-×-isSemiring
    ; *-comm     = ×-comm
    }
------------------------------------------------------------------------
-- Algebraic bundles

  ×-magma : Magma (suc ℓ) ℓ
  ×-magma = record
    { isMagma = ×-isMagma
    }

  ×-semigroup : Semigroup (suc ℓ) ℓ
  ×-semigroup = record
    { isSemigroup = ×-isSemigroup
    }

  ×-monoid : Monoid (suc ℓ) ℓ
  ×-monoid = record
    { isMonoid = ×-isMonoid
    }

  ×-commutativeMonoid : CommutativeMonoid (suc ℓ) ℓ
  ×-commutativeMonoid = record
    { isCommutativeMonoid = ×-isCommutativeMonoid
    }

  ×-⊎-commutativeSemiring : CommutativeSemiring (suc ℓ) ℓ
  ×-⊎-commutativeSemiring = record
    { isCommutativeSemiring = ⊎-×-isCommutativeSemiring
    }

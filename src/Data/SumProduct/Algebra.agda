------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums and products together
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.SumProduct.Algebra where

open import Algebra
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product as Prod using (_,_; _×_; uncurry; curry)
open import Data.Product.Algebra
open import Data.Product.Properties
open import Data.Sum as Sum
open import Data.Sum.Algebra
open import Data.Sum.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘′_; _∘_)
open import Level using (Level)

open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Definitions as FuncDef

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence; cong′)

------------------------------------------------------------------------
-- Setup

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

------------------------------------------------------------------------
-- Properties of × and ⊎

-- × distributes over ⊎

×-distribˡ-⊎ : ∀ ℓ → _DistributesOverˡ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribˡ-⊎ ℓ _ _ _ = inverse
  (uncurry λ x → [ inj₁ ∘′ (x ,_) , inj₂ ∘′ (x ,_) ]′)
  [ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]′
  [ cong′ , cong′ ]
  (uncurry λ _ → Sum.[ cong′ , cong′ ])

×-distribʳ-⊎ : ∀ ℓ → _DistributesOverʳ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribʳ-⊎ ℓ _ _ _ = inverse
  (uncurry [ curry inj₁ , curry inj₂ ]′)
  [ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]′
  [ cong′ , cong′ ]
  (uncurry [ (λ _ → cong′) , (λ _ → cong′) ])

×-distrib-⊎ : ∀ ℓ → _DistributesOver_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distrib-⊎ ℓ = ×-distribˡ-⊎ ℓ , ×-distribʳ-⊎ ℓ

------------------------------------------------------------------------
-- ⊥, ⊤, _×_ and _⊎_ form a commutative semiring

×-⊎-isSemiringWithoutAnnihilatingZero : (ℓ : Level) →
  IsSemiringWithoutAnnihilatingZero _↔_ _⊎_ _×_ ⊥ ⊤
×-⊎-isSemiringWithoutAnnihilatingZero ℓ = record
  { +-isCommutativeMonoid = ⊎-isCommutativeMonoid ℓ
  ; *-isMonoid = ×-isMonoid ℓ
  ; distrib = ×-distrib-⊎ ℓ
  }

×-⊎-isSemiring : (ℓ : Level) → IsSemiring _↔_ _⊎_ _×_ ⊥ ⊤
×-⊎-isSemiring ℓ = record
  { isSemiringWithoutAnnihilatingZero = ×-⊎-isSemiringWithoutAnnihilatingZero ℓ
  ; zero = ×-zero ℓ
  }

×-⊎-isCommutativeSemiring : (ℓ : Level) → IsCommutativeSemiring _↔_ _⊎_ _×_ ⊥ ⊤
×-⊎-isCommutativeSemiring ℓ = record
  { isSemiring = ×-⊎-isSemiring ℓ
  ; *-comm = ×-comm
  }

×-⊎-commutativeSemiring : (ℓ : Level) →
                          CommutativeSemiring (Level.suc ℓ) ℓ
×-⊎-commutativeSemiring ℓ = record
  { isCommutativeSemiring = ×-⊎-isCommutativeSemiring ℓ
  }

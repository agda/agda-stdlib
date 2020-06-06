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
open import Data.Product.Properties
open import Data.Sum as Sum
open import Data.Sum.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘′_; _∘_)
open import Level using (Level)

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
-- Properties of × and ⊎

-- × distributes over ⊎

×-distribˡ-⊎ : ∀ ℓ → _DistributesOverˡ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribˡ-⊎ ℓ _ _ _ = inverse
  (uncurry λ x → [ inj₁ ∘′ (x ,_) , inj₂ ∘′ (x ,_) ]′)
  [ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]′
  [ irefl , irefl ]
  (uncurry λ _ → Sum.[ irefl , irefl ])

×-distribʳ-⊎ : ∀ ℓ → _DistributesOverʳ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribʳ-⊎ ℓ _ _ _ = inverse
  (uncurry [ curry inj₁ , curry inj₂ ]′)
  [ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]′
  [ irefl , irefl ]
  (uncurry [ (λ _ → irefl) , (λ _ → irefl) ])

×-distrib-⊎ : ∀ ℓ → _DistributesOver_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distrib-⊎ ℓ = ×-distribˡ-⊎ ℓ , ×-distribʳ-⊎ ℓ

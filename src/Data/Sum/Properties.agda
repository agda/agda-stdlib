------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Properties where

open import Data.Sum
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

module _ {a b} {A : Set a} {B : Set b} where

  inj₁-injective : ∀ {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  inj₁-injective refl = refl

  inj₂-injective : ∀ {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  inj₂-injective refl = refl

  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = A ⊎ B} _≡_
  ≡-dec dec₁ dec₂ (inj₁ x) (inj₁ y) with dec₁ x y
  ... | yes refl = yes refl
  ... | no  x≢y  = no (x≢y ∘ inj₁-injective)
  ≡-dec dec₁ dec₂ (inj₁ x) (inj₂ y) = no λ()
  ≡-dec dec₁ dec₂ (inj₂ x) (inj₁ y) = no λ()
  ≡-dec dec₁ dec₂ (inj₂ x) (inj₂ y) with dec₂ x y
  ... | yes refl = yes refl
  ... | no  x≢y  = no (x≢y ∘ inj₂-injective)

  swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
  swap-involutive = [ (λ _ → refl) , (λ _ → refl) ]

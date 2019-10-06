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
open import Relation.Nullary.Decidable using (map′)

module _ {a b} {A : Set a} {B : Set b} where

  inj₁-injective : ∀ {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  inj₁-injective refl = refl

  inj₂-injective : ∀ {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  inj₂-injective refl = refl

  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = A ⊎ B} _≡_
  ≡-dec dec₁ dec₂ (inj₁ x) (inj₁ y) =
    map′ (cong inj₁) inj₁-injective (dec₁ x y)
  ≡-dec dec₁ dec₂ (inj₁ x) (inj₂ y) = no λ()
  ≡-dec dec₁ dec₂ (inj₂ x) (inj₁ y) = no λ()
  ≡-dec dec₁ dec₂ (inj₂ x) (inj₂ y) =
    map′ (cong inj₂) inj₂-injective (dec₂ x y)

  swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
  swap-involutive = [ (λ _ → refl) , (λ _ → refl) ]

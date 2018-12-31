------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties, related to products, that rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Properties.WithK where

open import Data.Product
open import Data.Product.Properties
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Equality

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveʳ : ∀ {a} {b c : B a} → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ,-injectiveʳ refl = refl

  ≡-dec : Decidable _≡_ → (∀ {a} → Decidable {A = B a} _≡_) →
          Decidable {A = Σ A B} _≡_
  ≡-dec dec₁ dec₂ (a , x) (b , y) with dec₁ a b
  ... | no  a≢b  = no (a≢b ∘ ,-injectiveˡ)
  ... | yes refl with dec₂ x y
  ...   | no x≢y   = no (x≢y ∘ ,-injectiveʳ)
  ...   | yes refl = yes refl

------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Properties where

open import Data.Product
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Product
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Equality (dependent)

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveˡ : ∀ {a c} {b : B a} {d : B c} → (a , b) ≡ (c , d) → a ≡ c
  ,-injectiveˡ refl = refl

  -- See also Data.Product.Properties.WithK.,-injectiveʳ.

------------------------------------------------------------------------
-- Equality (non-dependent)

module _ {a b} {A : Set a} {B : Set b} where

  ,-injectiveʳ : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → b ≡ d
  ,-injectiveʳ refl = refl

  ,-injective : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ,-injective refl = refl , refl

  ≡-dec : Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
          Decidable {A = A × B} _≡_
  ≡-dec dec₁ dec₂ (a , b) (c , d) =
    Dec.map′ (uncurry (cong₂ _,_)) ,-injective (dec₁ a c ×-dec dec₂ b d)

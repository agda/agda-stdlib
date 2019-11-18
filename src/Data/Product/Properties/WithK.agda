------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties, related to products, that rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Properties.WithK where

open import Data.Bool.Base
open import Data.Product
open import Data.Product.Properties using (,-injectiveˡ)
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Reflects
open import Relation.Nullary using (Dec; _because_; yes; no)
open import Relation.Nullary.Decidable using (map′)

------------------------------------------------------------------------
-- Equality

module _ {a b} {A : Set a} {B : Set b} where

  ,-injective : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ,-injective refl = refl , refl

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveʳ : ∀ {a} {b c : B a} → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ,-injectiveʳ refl = refl

  -- Note: this is not an instance of `_×-dec_`, because we need `x` and `y`
  -- to have the same type before we can test them for equality.
  ≡-dec : Decidable _≡_ → (∀ {a} → Decidable {A = B a} _≡_) →
          Decidable {A = Σ A B} _≡_
  ≡-dec dec₁ dec₂ (a , x) (b , y) with dec₁ a b
  ... | false because [a≢b] = no (invert [a≢b] ∘ ,-injectiveˡ)
  ... | yes refl = map′ (cong (a ,_)) ,-injectiveʳ (dec₂ x y)

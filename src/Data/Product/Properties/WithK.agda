------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties, related to products, that rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Properties.WithK where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Equality

-- These exports are deprecated from v1.4
open import Data.Product.Properties using (,-injective; ≡-dec) public

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveʳ : ∀ {a} {b c : B a} → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ,-injectiveʳ refl = refl

------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Product.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveˡ : ∀ {a c} {b : B a} {d : B c} → (a , b) ≡ (c , d) → a ≡ c
  ,-injectiveˡ refl = refl

  -- See also Data.Product.Properties.WithK.,-injectiveʳ.

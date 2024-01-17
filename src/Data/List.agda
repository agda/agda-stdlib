------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists
------------------------------------------------------------------------

-- See README.Data.List for examples of how to use and reason about
-- lists.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List where

import Data.List.NonEmpty.Base as List⁺
import Data.List.Properties as List
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl; cong₂; _≗_)

------------------------------------------------------------------------
-- Types and basic operations

open import Data.List.Base public hiding (scanr)

------------------------------------------------------------------------
-- scanr

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (e : B) where

  open List⁺ using (List⁺; _∷_; toList)

-- definition

  scanr : List A → List B
  scanr = toList ∘ go where
    go : List A → List⁺ B
    go []       = e ∷ []
    go (x ∷ xs) = let y ∷ ys = go xs in f x y ∷ y ∷ ys

-- property

  scanr-defn : scanr ≗ map (foldr f e) ∘ tails
  scanr-defn []                 = refl
  scanr-defn (x ∷ [])           = refl
  scanr-defn (x ∷ y∷ys@(_ ∷ _)) = let eq = scanr-defn y∷ys in
    cong₂ (λ z → f x z ∷_) (List.∷-injectiveˡ eq) eq

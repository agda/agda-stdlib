------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: internal definitions not meant to be imported
-- by users of the standard library.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Distance.Levenshtein.Internal where

{-# WARNING_ON_IMPORT
"This is an internal module not meant for public consumption.
There are no backwards compatibility guarantees whatsoever on its content."
#-}

open import Data.Nat.Base using (ℕ; _≤_; _+_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

-- These definitions surely need to go somewhere else
Unique : ∀ {a ℓ} {A : Set a} (dist : A → A → ℕ → Set ℓ) → Set (a ⊔ ℓ)
Unique dist = ∀ x y k l → dist x y k → dist x y l → k ≡ l

Triangle : ∀ {a ℓ} {A : Set a} (dist : A → A → ℕ → Set ℓ) → Set (a ⊔ ℓ)
Triangle dist = ∀ x y z k l m → dist x y k → dist y z l → dist x z m → m ≤ k + l

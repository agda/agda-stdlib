------------------------------------------------------------------------
-- The Agda standard library
--
-- Sorted lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (TotalOrder)

module Data.List.Relation.Unary.Sorted.TotalOrder
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder totalOrder renaming (Carrier to A)

open import Data.List.Base as List using (List)
open import Data.List.Relation.Unary.Linked as LinkedBase using (Linked)
open import Data.Maybe.Base using (just)
open import Data.Maybe.Relation.Binary.Connected
open import Level using (_⊔_)
open import Relation.Unary using (Pred)

private
  variable
    x : A
    xs : List A

-----------------------------------------------------------------------
-- Definition

Sorted : Pred (List A) (a ⊔ ℓ₂)
Sorted xs = Linked _≤_ xs

------------------------------------------------------------------------
-- Operations

open LinkedBase public
  using
  ( head   -- Sorted (x ∷ y ∷ xs) → x ≤ y
  ; head′  -- Sorted (x ∷ xs) → Connected _≤_ (just x) (List.head xs)
  ; tail   -- Sorted (x ∷ xs) → Sorted xs
  ; _∷′_   -- Connected R (just x) (List.head xs) → Sorted xs → Sorted (x ∷ xs)
  )

lookup : Sorted xs → Connected _≤_ (just x) (List.head xs) →
         ∀ i → x ≤ List.lookup xs i
lookup = LinkedBase.lookup trans

------------------------------------------------------------------------
-- Properties of predicates preserved by Sorted

open LinkedBase public
  using
  ( irrelevant          -- : B.Irrelevant _≤_ → U.Irrelevant Sorted
  ; satisfiable         -- : U.Satisfiable Sorted
  )
  renaming
  ( linked? to sorted?  -- : B.Decidable _≤_ → U.Decidable Sorted
  )

------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Predomain.Definitions
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred)

private
  variable
    i : Level
    I : Set i
    z : A

------------------------------------------------------------------------
-- Lower bound
------------------------------------------------------------------------

LowerBound : (f : I → A) → Pred A _
LowerBound f x = ∀ i → x ≤ f i

------------------------------------------------------------------------
-- Upper bound
------------------------------------------------------------------------

UpperBound : (f : I → A) → Pred A _
UpperBound f y = ∀ i → f i ≤ y

------------------------------------------------------------------------
-- Minimal upper bound above a given element
------------------------------------------------------------------------

record MinimalUpperBoundAbove
  {I : Set i} (f : I → A) (x y : A) : Set (a ⊔ i ⊔ ℓ) where
  field
    lowerBound : x ≤ y
    upperBound : UpperBound {I = I} f y
    minimal    : x ≤ z → UpperBound f z → y ≤ z
    

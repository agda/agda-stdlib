------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations, relative to an apartness relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Apartness.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_#_ : Rel A ℓ)     -- The underlying apartness
  where

open import Algebra.Core using (Op₁; Op₂)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_on_)


------------------------------------------------------------------------
-- Properties of operations

module _ (f : Op₁ A) where

  StronglyCongruent₁  : Set _
  StronglyCongruent₁  = (_#_ on f) ⇒ _#_ 

module _ (_∙_ : Op₂ A) where

  StronglyCongruent₂ : Set _
  StronglyCongruent₂ =
    (∀ x → StronglyCongruent₁ (x ∙_)) × (∀ z → StronglyCongruent₁ (_∙ z))

  StronglyExtensional : Set _
  StronglyExtensional = ∀ {x y w z} → (x ∙ y) # (w ∙ z) → x # w ⊎ y # z


------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)
open import Data.W using (W)

module Data.Container where

------------------------------------------------------------------------
-- Re-exporting content to maintain backwards compatibility

open import Data.Container.Core public
open import Data.Container.Relation.Unary.Any
  using (◇) renaming (map to ◇-map) public
open import Data.Container.Relation.Unary.All
  using (□) renaming (map to □-map) public
open import Data.Container.Membership
  using (_∈_) public
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (Pointwise to Eq) public
open import Data.Container.Relation.Binary.Pointwise.Properties
  using (refl; sym; trans) public
open import Data.Container.Relation.Binary.Equality.Setoid
  using (isEquivalence; setoid) public
open import Data.Container.Properties
  using () renaming (map-identity to identity; map-compose to composition) public
open import Data.Container.Related public

module Morphism where

  open import Data.Container.Morphism.Properties
    using (Natural; NT; natural; complete; id-correct; ∘-correct) public

  open import Data.Container.Morphism
    using (id; _∘_) public

-- The least fixpoint of a container.

μ : ∀ {s p} → Container s p → Set (s ⊔ p)
μ = W

-- The greatest fixpoint of a container can be found
-- in `Data.Container.GreatestFixpoint` as it uses unsafe
-- sized types.

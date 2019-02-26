------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container where

open import Level using (_⊔_; suc)
open import Codata.Musical.M hiding (map)
open import Data.Container.Membership
open import Data.Container.Relation.Binary.Pointwise using (Pointwise)
import Data.Container.Relation.Binary.Pointwise.Properties as Pw
open import Data.Product as Prod hiding (map)
open import Data.W hiding (map)

open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
import Function.Related as Related

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Unary using (Pred ; _⊆_)

------------------------------------------------------------------------
-- Containers

-- A container is a set of shapes, and for every shape a set of positions.

open import Data.Container.Core public

-- The least and greatest fixpoints of a container.

μ : ∀ {s p} → Container s p → Set (s ⊔ p)
μ = W

ν : ∀ {s p} → Container s p → Set (s ⊔ p)
ν = M

------------------------------------------------------------------------
-- Functoriality

-- Containers are functors.

map : ∀ {s p x y} {C : Container s p} {X : Set x} {Y : Set y} →
      (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map₂ (f ⟨∘⟩_)

----------
open Related public
  using (Kind; Symmetric-kind)
  renaming ( implication         to subset
           ; reverse-implication to superset
           ; equivalence         to set
           ; injection           to subbag
           ; reverse-injection   to superbag
           ; bijection           to bag
           )

[_]-Order : ∀ {s p ℓ} → Kind → Container s p → Set ℓ →
            Preorder (s ⊔ p ⊔ ℓ) (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
[ k ]-Order C X = Related.InducedPreorder₂ k (_∈_ {C = C} {X = X})

[_]-Equality : ∀ {s p ℓ} → Symmetric-kind → Container s p → Set ℓ →
               Setoid (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
[ k ]-Equality C X = Related.InducedEquivalence₂ k (_∈_ {C = C} {X = X})

infix 4 _∼[_]_
_∼[_]_ : ∀ {s p x} {C : Container s p} {X : Set x} →
         ⟦ C ⟧ X → Kind → ⟦ C ⟧ X → Set (p ⊔ x)
_∼[_]_ {C = C} {X} xs k ys = Preorder._∼_ ([ k ]-Order C X) xs ys

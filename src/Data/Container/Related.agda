------------------------------------------------------------------------
-- The Agda standard library
--
-- Several kinds of "relatedness" for containers such as equivalences,
-- surjections and bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Related where

open import Level using (_⊔_)
open import Data.Container.Core
import Function.Related as Related
open import Relation.Binary
open import Data.Container.Membership

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

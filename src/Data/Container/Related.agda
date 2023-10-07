------------------------------------------------------------------------
-- The Agda standard library
--
-- Several kinds of "relatedness" for containers such as equivalences,
-- surjections and bijections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Related where

open import Level using (_⊔_)
open import Data.Container.Core
import Function.Related.Propositional as Related
open import Relation.Binary.Bundles using (Preorder; Setoid)
open import Data.Container.Membership

open Related public
  using (Kind; SymmetricKind)
  renaming ( implication         to subset
           ; reverseImplication  to superset
           ; equivalence         to set
           ; injection           to subbag
           ; reverseInjection    to superbag
           ; bijection           to bag
           )

[_]-Order : ∀ {s p ℓ} → Kind → Container s p → Set ℓ →
            Preorder (s ⊔ p ⊔ ℓ) (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
[ k ]-Order C X = Related.InducedPreorder₂ k (_∈_ {C = C} {X = X})

[_]-Equality : ∀ {s p ℓ} → SymmetricKind → Container s p → Set ℓ →
               Setoid (s ⊔ p ⊔ ℓ) (p ⊔ ℓ)
[ k ]-Equality C X = Related.InducedEquivalence₂ k (_∈_ {C = C} {X = X})

infix 4 _≲[_]_
_≲[_]_ : ∀ {s p x} {C : Container s p} {X : Set x} →
         ⟦ C ⟧ X → Kind → ⟦ C ⟧ X → Set (p ⊔ x)
_≲[_]_ {C = C} {X} xs k ys = Preorder._≲_ ([ k ]-Order C X) xs ys



------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

infix 4 _∼[_]_
_∼[_]_ = _≲[_]_
{-# WARNING_ON_USAGE _∼[_]_
"Warning: _∼[_]_ was deprecated in v2.0. Please use _≲[_]_ instead. "
#-}

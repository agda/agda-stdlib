------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by preorders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.Preorder
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Function
open import Data.Product as Prod
open import Relation.Binary.InducedStructures
     renaming ( InducedSetoid to ISetoid
              ; InducedPoset to IPoset
              )

open Relation.Binary.Preorder P

-- The inverse relation is also a preorder.

invIsPreorder : IsPreorder _≈_ (flip _∼_)
invIsPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = reflexive ∘ Eq.sym
  ; trans         = flip trans
  }

invPreorder : Preorder p₁ p₂ p₃
invPreorder = record { isPreorder = invIsPreorder }

------------------------------------------------------------------------
-- For every preorder there is an induced equivalence

InducedEquivalence : Setoid _ _
InducedEquivalence = ISetoid _∼_ refl trans

------------------------------------------------------------------------
-- For every preorder there is an induced poset over InducedEquivalence

InducedPoset : Poset _ _ _
InducedPoset = IPoset _∼_ refl trans

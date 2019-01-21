------------------------------------------------------------------------
-- The Agda standard library
--
-- A pointwise lifting of a relation to incorporate a new supremum.
------------------------------------------------------------------------

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Supremum

open import Relation.Binary

module Relation.Binary.Construct.Add.Supremum.Equality
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Relation.Binary.Construct.Add.Point.Equality _≈_ public
  renaming
  (_≈∙_                 to _≈⁺_
  ; ∙≈∙                 to ⊤⁺≈⊤⁺
  ; ≈∙-refl             to ≈⁺-refl
  ; ≈∙-sym              to ≈⁺-sym
  ; ≈∙-trans            to ≈⁺-trans
  ; ≈∙-dec              to ≈⁺-dec
  ; ≈∙-irrelevant       to ≈⁺-irrelevant
  ; ≈∙-substitutive     to ≈⁺-substitutive
  ; ≈∙-isEquivalence    to ≈⁺-isEquivalence
  ; ≈∙-isDecEquivalence to ≈⁺-isDecEquivalence
  )

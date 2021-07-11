------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Algebra.Lattice.Properties.Lattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Lattice.Bundles
open import Relation.Binary
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product using (_,_; swap)

module Algebra.Properties.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open import Algebra.Lattice.Properties.Lattice L public

{-# WARNING_ON_IMPORT
"Algebra.Properties.Lattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.Lattice instead."
#-}


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

open Lattice L

-- Version 1.1

∧-idempotent = ∧-idem
{-# WARNING_ON_USAGE ∧-idempotent
"Warning: ∧-idempotent was deprecated in v1.1.
Please use ∧-idem instead."
#-}
∨-idempotent = ∨-idem
{-# WARNING_ON_USAGE ∨-idempotent
"Warning: ∨-idempotent was deprecated in v1.1.
Please use ∨-idem instead."
#-}
isOrderTheoreticLattice = ∨-∧-isOrderTheoreticLattice
{-# WARNING_ON_USAGE isOrderTheoreticLattice
"Warning: isOrderTheoreticLattice was deprecated in v1.1.
Please use ∨-∧-isOrderTheoreticLattice instead."
#-}
orderTheoreticLattice = ∨-∧-orderTheoreticLattice
{-# WARNING_ON_USAGE orderTheoreticLattice
"Warning: orderTheoreticLattice was deprecated in v1.1.
Please use ∨-∧-orderTheoreticLattice instead."
#-}

-- Version 1.4

replace-equality : {_≈′_ : Rel Carrier l₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) → Lattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { isLattice = record
    { isEquivalence = record
      { refl  = to ⟨$⟩ refl
      ; sym   = λ x≈y → to ⟨$⟩ sym (from ⟨$⟩ x≈y)
      ; trans = λ x≈y y≈z → to ⟨$⟩ trans (from ⟨$⟩ x≈y) (from ⟨$⟩ y≈z)
      }
    ; ∨-comm     = λ x y → to ⟨$⟩ ∨-comm x y
    ; ∨-assoc    = λ x y z → to ⟨$⟩ ∨-assoc x y z
    ; ∨-cong     = λ x≈y u≈v → to ⟨$⟩ ∨-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; ∧-comm     = λ x y → to ⟨$⟩ ∧-comm x y
    ; ∧-assoc    = λ x y z → to ⟨$⟩ ∧-assoc x y z
    ; ∧-cong     = λ x≈y u≈v → to ⟨$⟩ ∧-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; absorptive = (λ x y → to ⟨$⟩ ∨-absorbs-∧ x y)
                 , (λ x y → to ⟨$⟩ ∧-absorbs-∨ x y)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
{-# WARNING_ON_USAGE replace-equality
"Warning: replace-equality was deprecated in v1.4.
Please use isLattice from `Algebra.Construct.Subst.Equality` instead."
#-}

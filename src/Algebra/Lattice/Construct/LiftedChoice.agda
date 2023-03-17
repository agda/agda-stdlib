------------------------------------------------------------------------
-- The Agda standard library
--
-- Choosing between elements based on the result of applying a function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra
open import Algebra.Lattice
open import Algebra.Construct.LiftedChoice
open import Relation.Binary
open import Level using (Level)

module Algebra.Lattice.Construct.LiftedChoice where

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Structures

module _ {_≈_ : Rel B ℓ} {_∙_ : Op₂ B}
         (∙-isSelectiveMagma : IsSelectiveMagma _≈_ _∙_)
         {_≈′_ : Rel A ℓ} {f : A → B}
         (f-injective : ∀ {x y} → f x ≈ f y → x ≈′ y)
         (f-cong : f Preserves _≈′_ ⟶ _≈_)
         (≈′-isEquivalence : IsEquivalence _≈′_)
         where

  open IsSelectiveMagma ∙-isSelectiveMagma renaming (sel to ∙-sel)

  private
    _◦_ = Lift _≈_ _∙_ ∙-sel f

  isSemilattice : Associative _≈_ _∙_ → Commutative _≈_ _∙_ →
                  IsSemilattice _≈′_ _◦_
  isSemilattice ∙-assoc ∙-comm = record
    { isBand = isBand ∙-isSelectiveMagma f-injective f-cong ≈′-isEquivalence ∙-assoc
    ; comm   = comm   ∙-isSelectiveMagma (λ {x} → f-injective {x}) ∙-comm
    }

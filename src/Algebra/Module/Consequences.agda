------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of scaling and other operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Consequences where

open import Algebra.Core using (Op₂)
import Algebra.Definitions as Defs
open import Algebra.Module.Core using (Opₗ; Opᵣ)
open import Algebra.Module.Definitions
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b c ℓ ℓa : Level
    A : Set a
    B : Set b

module _ (_≈ᴬ_ : Rel {a} A ℓa) (S : Setoid c ℓ) where

  open Setoid S
  open ≈-Reasoning S
  open Defs _≈ᴬ_

  private
    module L = LeftDefs A _≈_
    module R = RightDefs A _≈_
    module B = BiDefs A A _≈_

  module _ {_*_ : Op₂ A} {_*ₗ_ : Opₗ A Carrier} where

    private
      _*ᵣ_ = flip _*ₗ_

    *ₗ-assoc∧comm⇒*ᵣ-assoc :
      L.RightCongruent _≈ᴬ_ _*ₗ_ →
      L.Associative _*_ _*ₗ_ → Commutative _*_ → R.Associative _*_ _*ᵣ_
    *ₗ-assoc∧comm⇒*ᵣ-assoc *ₗ-congʳ *ₗ-assoc *-comm m x y = begin
      (m *ᵣ x) *ᵣ y  ≈⟨ refl ⟩
      y *ₗ (x *ₗ m)  ≈⟨ *ₗ-assoc _ _ _ ⟨
      (y * x) *ₗ m   ≈⟨ *ₗ-congʳ (*-comm y x) ⟩
      (x * y) *ₗ m   ≈⟨ refl ⟩
      m *ᵣ (x * y)   ∎

    *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc :
      L.RightCongruent _≈ᴬ_ _*ₗ_ →
      L.Associative _*_ _*ₗ_ → Commutative _*_ → B.Associative _*ₗ_ _*ᵣ_
    *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc *ₗ-congʳ *ₗ-assoc *-comm x m y = begin
      ((x *ₗ m) *ᵣ y)  ≈⟨ refl ⟩
      (y *ₗ (x *ₗ m))  ≈⟨ *ₗ-assoc _ _ _ ⟨
      ((y * x) *ₗ m)   ≈⟨ *ₗ-congʳ (*-comm y x) ⟩
      ((x * y) *ₗ m)   ≈⟨ *ₗ-assoc _ _ _ ⟩
      (x *ₗ (y *ₗ m))  ≈⟨ refl ⟩
      (x *ₗ (m *ᵣ y))  ∎

  module _ {_*_ : Op₂ A} {_*ᵣ_ : Opᵣ A Carrier} where

    private
      _*ₗ_ = flip _*ᵣ_

    *ᵣ-assoc∧comm⇒*ₗ-assoc :
      R.LeftCongruent _≈ᴬ_ _*ᵣ_ →
      R.Associative _*_ _*ᵣ_ → Commutative _*_ → L.Associative _*_ _*ₗ_
    *ᵣ-assoc∧comm⇒*ₗ-assoc *ᵣ-congˡ *ᵣ-assoc *-comm x y m = begin
      ((x * y) *ₗ m)   ≈⟨ refl ⟩
      (m *ᵣ (x * y))   ≈⟨ *ᵣ-congˡ (*-comm x y) ⟩
      (m *ᵣ (y * x))   ≈⟨ *ᵣ-assoc _ _ _ ⟨
      ((m *ᵣ y) *ᵣ x)  ≈⟨ refl ⟩
      (x *ₗ (y *ₗ m))  ∎

    *ᵣ-assoc∧comm⇒*ₗ-*ᵣ-assoc :
      R.LeftCongruent _≈ᴬ_ _*ᵣ_ →
      R.Associative _*_ _*ᵣ_ → Commutative _*_ → B.Associative _*ₗ_ _*ᵣ_
    *ᵣ-assoc∧comm⇒*ₗ-*ᵣ-assoc *ᵣ-congˡ *ᵣ-assoc *-comm x m y = begin
      ((x *ₗ m) *ᵣ y)  ≈⟨ refl ⟩
      ((m *ᵣ x) *ᵣ y)  ≈⟨ *ᵣ-assoc _ _ _ ⟩
      (m *ᵣ (x * y))   ≈⟨ *ᵣ-congˡ (*-comm x y) ⟩
      (m *ᵣ (y * x))   ≈⟨ *ᵣ-assoc _ _ _ ⟨
      ((m *ᵣ y) *ᵣ x)  ≈⟨ refl ⟩
      (x *ₗ (m *ᵣ y))  ∎


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

*ₗ-assoc+comm⇒*ᵣ-assoc = *ₗ-assoc∧comm⇒*ᵣ-assoc
{-# WARNING_ON_USAGE *ₗ-assoc+comm⇒*ᵣ-assoc
"Warning: *ₗ-assoc+comm⇒*ᵣ-assoc was deprecated in v2.3.
Please use *ₗ-assoc∧comm⇒*ᵣ-assoc instead."
#-}

*ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc = *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc
{-# WARNING_ON_USAGE *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc
"Warning: *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc was deprecated in v2.3.
Please use *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc instead."
#-}

*ᵣ-assoc+comm⇒*ₗ-assoc = *ᵣ-assoc∧comm⇒*ₗ-assoc
{-# WARNING_ON_USAGE *ᵣ-assoc+comm⇒*ₗ-assoc
"Warning: *ᵣ-assoc+comm⇒*ₗ-assoc was deprecated in v2.3.
Please use *ᵣ-assoc∧comm⇒*ₗ-assoc instead."
#-}

*ᵣ-assoc+comm⇒*ₗ-*ᵣ-assoc = *ᵣ-assoc∧comm⇒*ₗ-*ᵣ-assoc
{-# WARNING_ON_USAGE *ᵣ-assoc+comm⇒*ₗ-*ᵣ-assoc
"Warning: *ᵣ-assoc+comm⇒*ₗ-*ᵣ-assoc was deprecated in v2.3.
Please use *ᵣ-assoc∧comm⇒*ₗ-*ᵣ-assoc instead."
#-}

------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of bijections.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Bijection where

open import Function.Bundles using (Bijection; Inverse; Equivalence;
  _⤖_; _↔_; _⇔_)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Trans)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Properties.Inverse
  using (Inverse⇒Bijection; Inverse⇒Equivalence)

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    T S : Setoid a ℓ

------------------------------------------------------------------------
-- Conversion functions

Bijection⇒Inverse : Bijection S T → Inverse S T
Bijection⇒Inverse bij = record
  { to        = to
  ; from      = section
  ; to-cong   = cong
  ; from-cong = Symmetry.section-cong bijective Eq₁.refl Eq₂.sym Eq₂.trans
  ; inverse   = section-inverseˡ
              , λ y≈to[x] → injective (Eq₂.trans (section-strictInverseˡ _) y≈to[x])
  }
  where open Bijection bij

Bijection⇒Equivalence : Bijection T S → Equivalence T S
Bijection⇒Equivalence = Inverse⇒Equivalence ∘ Bijection⇒Inverse

------------------------------------------------------------------------
-- Setoid properties

refl : Reflexive (Bijection {a} {ℓ})
refl = Identity.bijection _

-- Now we *can* prove full symmetry as we now have a proof that
-- the witness produced by the surjection proof preserves equality
sym : Bijection S T → Bijection T S
sym = Inverse⇒Bijection ∘ Symmetry.inverse ∘ Bijection⇒Inverse

trans : Trans (Bijection {a} {ℓ₁} {b} {ℓ₂}) (Bijection {b} {ℓ₂} {c} {ℓ₃}) Bijection
trans = Composition.bijection

------------------------------------------------------------------------
-- Propositional properties

⤖-isEquivalence : IsEquivalence {ℓ = ℓ} _⤖_
⤖-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

⤖⇒↔ : A ⤖ B → A ↔ B
⤖⇒↔ = Bijection⇒Inverse

⤖⇒⇔ : A ⤖ B → A ⇔ B
⤖⇒⇔ = Bijection⇒Equivalence


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

open Symmetry public
  using ()
  renaming (bijection-≡ to sym-≡)
{-# WARNING_ON_USAGE sym-≡
"Warning: sym-≡ was deprecated in v2.3.
Please use sym instead. "
#-}

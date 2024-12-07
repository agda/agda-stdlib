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
open import Function.Properties.Surjection using (injective⇒to⁻-cong)
open import Function.Properties.Inverse using (Inverse⇒Equivalence)

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    T S : Setoid a ℓ

------------------------------------------------------------------------
-- Setoid properties

refl : Reflexive (Bijection {a} {ℓ})
refl = Identity.bijection _

-- Can't prove full symmetry as we have no proof that the witness
-- produced by the surjection proof preserves equality
sym-≡ : Bijection S (setoid B) → Bijection (setoid B) S
sym-≡ = Symmetry.bijection-≡

trans : Trans (Bijection {a} {ℓ₁} {b} {ℓ₂}) (Bijection {b} {ℓ₂} {c} {ℓ₃}) Bijection
trans = Composition.bijection

------------------------------------------------------------------------
-- Propositional properties

⤖-isEquivalence : IsEquivalence {ℓ = ℓ} _⤖_
⤖-isEquivalence = record
  { refl  = refl
  ; sym   = sym-≡
  ; trans = trans
  }

------------------------------------------------------------------------
-- Conversion functions

Bijection⇒Inverse : Bijection S T → Inverse S T
Bijection⇒Inverse bij = record
  { to        = to
  ; from      = to⁻
  ; to-cong   = cong
  ; from-cong = injective⇒to⁻-cong surjection injective
  ; inverse   = (λ y≈to⁻[x] → Eq₂.trans (cong y≈to⁻[x]) (to∘to⁻ _)) ,
                (λ y≈to[x] → injective (Eq₂.trans (to∘to⁻ _) y≈to[x]))
  }
  where open Bijection bij; to∘to⁻ = proj₂ ∘ strictlySurjective

Bijection⇒Equivalence : Bijection T S → Equivalence T S
Bijection⇒Equivalence = Inverse⇒Equivalence ∘ Bijection⇒Inverse

⤖⇒↔ : A ⤖ B → A ↔ B
⤖⇒↔ = Bijection⇒Inverse

⤖⇒⇔ : A ⤖ B → A ⇔ B
⤖⇒⇔ = Bijection⇒Equivalence

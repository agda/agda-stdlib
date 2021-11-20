------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of bijections.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Bijection where

open import Function.Bundles
open import Level using (Level)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality as P using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Base using (_∘_)
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
sym-≡ : Bijection S (P.setoid B) → Bijection (P.setoid B) S
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
Bijection⇒Inverse {S = S} {T = T} b = record
  { f     = f
  ; f⁻¹   = f⁻
  ; cong₁ = cong
  ; cong₂ = λ {x} {y} x≈y → injective (begin
      f (f⁻ x)  ≈⟨ f∘f⁻ x ⟩
      x         ≈⟨ x≈y ⟩
      y         ≈˘⟨ f∘f⁻ y ⟩
      f (f⁻ y)  ∎)
  ; inverse = f∘f⁻ , injective ∘ f∘f⁻ ∘ f
  }
  where open SetoidReasoning T; open Bijection b; f∘f⁻ = proj₂ ∘ surjective

Bijection⇒Equivalence : Bijection T S → Equivalence T S
Bijection⇒Equivalence = Inverse⇒Equivalence ∘ Bijection⇒Inverse

⤖⇒↔ : A ⤖ B → A ↔ B
⤖⇒↔ = Bijection⇒Inverse

⤖⇒⇔ : A ⤖ B → A ⇔ B
⤖⇒⇔ = Bijection⇒Equivalence


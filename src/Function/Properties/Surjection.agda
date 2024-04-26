------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of surjections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Surjection where

open import Function.Base using (_∘_; _$_)
open import Function.Definitions using (Surjective; Injective; Congruent)
open import Function.Bundles using (Func; Surjection; _↠_; _⟶_; _↪_; mk↪;
  _⇔_; mk⇔)
import Function.Construct.Identity as Identity
import Function.Construct.Composition as Compose
open import Level using (Level)
open import Data.Product.Base using (proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.Definitions using (Reflexive; Trans)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    T S : Setoid a ℓ

------------------------------------------------------------------------
-- Constructors

mkSurjection : (f : Func S T) (open Func f) →
              Surjective Eq₁._≈_ Eq₂._≈_ to  →
              Surjection S T
mkSurjection f surjective = record
  { Func f
  ; surjective = surjective
  }

------------------------------------------------------------------------
-- Conversion functions

↠⇒⟶ : A ↠ B → A ⟶ B
↠⇒⟶ = Surjection.function

↠⇒↪ : A ↠ B → B ↪ A
↠⇒↪ s = mk↪ {from = to} λ { ≡.refl → proj₂ (strictlySurjective _)}
  where open Surjection s

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ s = mk⇔ to (proj₁ ∘ surjective)
  where open Surjection s

------------------------------------------------------------------------
-- Setoid properties

refl : Reflexive (Surjection {a} {ℓ})
refl {x = x} = Identity.surjection x

trans : Trans (Surjection {a} {ℓ₁} {b} {ℓ₂})
              (Surjection {b} {ℓ₂} {c} {ℓ₃})
              (Surjection {a} {ℓ₁} {c} {ℓ₃})
trans = Compose.surjection

------------------------------------------------------------------------
-- Other

injective⇒to⁻-cong : (surj : Surjection S T) →
                      (open Surjection surj) →
                      Injective Eq₁._≈_ Eq₂._≈_ to →
                      Congruent Eq₂._≈_ Eq₁._≈_ to⁻
injective⇒to⁻-cong {T = T} surj injective {x} {y} x≈y = injective $ begin
  to (to⁻ x) ≈⟨ to∘to⁻ x ⟩
  x          ≈⟨ x≈y ⟩
  y          ≈⟨ to∘to⁻ y ⟨
  to (to⁻ y) ∎
  where
  open ≈-Reasoning T
  open Surjection surj


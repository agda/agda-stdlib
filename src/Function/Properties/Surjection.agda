------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of surjections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Surjection where

open import Function.Base using (_∘_; _$_)
open import Function.Definitions using (Surjective; Injective; Congruent)
open import Function.Bundles
  using (Func; Surjection; Bijection; _↠_; _⟶_; _↪_; mk↪; _⇔_; mk⇔)
import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Compose
open import Level using (Level)
open import Data.Product.Base using (_,_; proj₁; proj₂)
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
↠⇒↪ s = mk↪ {from = to} λ { ≡.refl → strictlyInverseˡ _ }
  where open Surjection s

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ s = mk⇔ to from
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
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

module _ (surjection : Surjection S T) where

  open Surjection surjection

  injective⇒to⁻-cong : Injective Eq₁._≈_ Eq₂._≈_ to →
                       Congruent Eq₂._≈_ Eq₁._≈_ from
  injective⇒to⁻-cong injective = from-cong
    where
    SB : Bijection S T
    SB = record { cong = cong ; bijective = injective , surjective }
    open Bijection (Symmetry.bijectionWithoutCongruence SB)
      using () renaming (cong to from-cong)
{-# WARNING_ON_USAGE injective⇒to⁻-cong
"Warning: injective⇒to⁻-cong was deprecated in v2.3.
Please use Function.Construct.Symmetry.bijectionWithoutCongruence instead. "
#-}

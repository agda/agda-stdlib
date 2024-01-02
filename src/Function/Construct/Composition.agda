------------------------------------------------------------------------
-- The Agda standard library
--
-- Composition of functional properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Construct.Composition where

open import Data.Product.Base as Product using (_,_)
open import Function.Base using (_∘_; flip)
open import Function.Bundles
open import Function.Definitions
open import Function.Structures
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set a

------------------------------------------------------------------------
-- Properties

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈₃ : Rel C ℓ₃)
         {f : A → B} {g : B → C}
         where

  congruent : Congruent ≈₁ ≈₂ f → Congruent ≈₂ ≈₃ g →
              Congruent ≈₁ ≈₃ (g ∘ f)
  congruent f-cong g-cong = g-cong ∘ f-cong

  injective : Injective ≈₁ ≈₂ f → Injective ≈₂ ≈₃ g →
              Injective ≈₁ ≈₃ (g ∘ f)
  injective f-inj g-inj = f-inj ∘ g-inj

  surjective : Surjective ≈₁ ≈₂ f → Surjective ≈₂ ≈₃ g →
               Surjective ≈₁ ≈₃ (g ∘ f)
  surjective f-sur g-sur x with g-sur x
  ... | y , gproof with f-sur y
  ...   | z , fproof = z , gproof ∘ fproof

  bijective : Bijective ≈₁ ≈₂ f → Bijective ≈₂ ≈₃ g →
              Bijective ≈₁ ≈₃ (g ∘ f)
  bijective = Product.zip′ injective surjective

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈₃ : Rel C ℓ₃)
         {f : A → B} {f⁻¹ : B → A} {g : B → C} {g⁻¹ : C → B}
         where

  inverseˡ : Inverseˡ ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₂ ≈₃ g g⁻¹ →
             Inverseˡ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseˡ f-inv g-inv = g-inv ∘ f-inv

  inverseʳ : Inverseʳ ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₂ ≈₃ g g⁻¹ →
             Inverseʳ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseʳ f-inv g-inv = f-inv ∘ g-inv

  inverseᵇ : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₂ ≈₃ g g⁻¹ →
             Inverseᵇ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseᵇ = Product.zip′ inverseˡ inverseʳ

------------------------------------------------------------------------
-- Structures

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {≈₃ : Rel C ℓ₃}
         {f : A → B} {g : B → C}
         where

  isCongruent : IsCongruent ≈₁ ≈₂ f → IsCongruent ≈₂ ≈₃ g →
                IsCongruent ≈₁ ≈₃ (g ∘ f)
  isCongruent f-cong g-cong = record
    { cong           = G.cong ∘ F.cong
    ; isEquivalence₁ = F.isEquivalence₁
    ; isEquivalence₂ = G.isEquivalence₂
    } where module F = IsCongruent f-cong; module G = IsCongruent g-cong

  isInjection : IsInjection ≈₁ ≈₂ f → IsInjection ≈₂ ≈₃ g →
                IsInjection ≈₁ ≈₃ (g ∘ f)
  isInjection f-inj g-inj = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; injective   = injective ≈₁ ≈₂ ≈₃ F.injective G.injective
    } where module F = IsInjection f-inj; module G = IsInjection g-inj

  isSurjection : IsSurjection ≈₁ ≈₂ f → IsSurjection ≈₂ ≈₃ g →
                 IsSurjection ≈₁ ≈₃ (g ∘ f)
  isSurjection f-surj g-surj = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; surjective  = surjective ≈₁ ≈₂ ≈₃ F.surjective G.surjective
    } where module F = IsSurjection f-surj; module G = IsSurjection g-surj

  isBijection : IsBijection ≈₁ ≈₂ f → IsBijection ≈₂ ≈₃ g →
                IsBijection ≈₁ ≈₃ (g ∘ f)
  isBijection f-bij g-bij = record
    { isInjection = isInjection F.isInjection G.isInjection
    ; surjective  = surjective ≈₁ ≈₂ ≈₃ F.surjective G.surjective
    } where module F = IsBijection f-bij; module G = IsBijection g-bij

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {≈₃ : Rel C ℓ₃}
         {f : A → B} {g : B → C} {f⁻¹ : B → A} {g⁻¹ : C → B}
         where

  isLeftInverse : IsLeftInverse ≈₁ ≈₂ f f⁻¹ → IsLeftInverse ≈₂ ≈₃ g g⁻¹ →
                  IsLeftInverse ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  isLeftInverse f-invˡ g-invˡ = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; from-cong   = congruent ≈₃ ≈₂ ≈₁ G.from-cong F.from-cong
    ; inverseˡ    = inverseˡ ≈₁ ≈₂ ≈₃ F.inverseˡ G.inverseˡ
    } where module F = IsLeftInverse f-invˡ; module G = IsLeftInverse g-invˡ

  isRightInverse : IsRightInverse ≈₁ ≈₂ f f⁻¹ → IsRightInverse ≈₂ ≈₃ g g⁻¹ →
                   IsRightInverse ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  isRightInverse f-invʳ g-invʳ = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; from-cong   = congruent ≈₃ ≈₂ ≈₁ G.from-cong F.from-cong
    ; inverseʳ    = inverseʳ ≈₁ ≈₂ ≈₃ F.inverseʳ G.inverseʳ
    } where module F = IsRightInverse f-invʳ; module G = IsRightInverse g-invʳ

  isInverse : IsInverse ≈₁ ≈₂ f f⁻¹ → IsInverse ≈₂ ≈₃ g g⁻¹ →
              IsInverse ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  isInverse f-inv g-inv = record
    { isLeftInverse = isLeftInverse F.isLeftInverse G.isLeftInverse
    ; inverseʳ      = inverseʳ ≈₁ ≈₂ ≈₃ F.inverseʳ G.inverseʳ
    } where module F = IsInverse f-inv; module G = IsInverse g-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} {T : Setoid c ℓ₃} where

  open Setoid renaming (_≈_ to ≈)

  function : Func R S → Func S T → Func R T
  function f g = record
    { to   = G.to ∘ F.to
    ; cong = congruent (≈ R) (≈ S) (≈ T) F.cong G.cong
    } where module F = Func f; module G = Func g

  injection : Injection R S → Injection S T → Injection R T
  injection inj₁ inj₂ = record
    { to        = G.to ∘ F.to
    ; cong      = congruent (≈ R) (≈ S) (≈ T) F.cong G.cong
    ; injective = injective (≈ R) (≈ S) (≈ T) F.injective G.injective
    } where module F = Injection inj₁; module G = Injection inj₂

  surjection : Surjection R S → Surjection S T → Surjection R T
  surjection surj₁ surj₂ = record
    { to         = G.to ∘ F.to
    ; cong       = congruent  (≈ R) (≈ S) (≈ T) F.cong G.cong
    ; surjective = surjective (≈ R) (≈ S) (≈ T) F.surjective G.surjective
    } where module F = Surjection surj₁; module G = Surjection surj₂

  bijection : Bijection R S → Bijection S T → Bijection R T
  bijection bij₁ bij₂ = record
    { to        = G.to ∘ F.to
    ; cong      = congruent (≈ R) (≈ S) (≈ T) F.cong G.cong
    ; bijective = bijective (≈ R) (≈ S) (≈ T) F.bijective G.bijective
    } where module F = Bijection bij₁; module G = Bijection bij₂

  equivalence : Equivalence R S → Equivalence S T → Equivalence R T
  equivalence equiv₁ equiv₂ = record
    { to        = G.to ∘ F.to
    ; from      = F.from ∘ G.from
    ; to-cong   = congruent (≈ R) (≈ S) (≈ T) F.to-cong G.to-cong
    ; from-cong = congruent (≈ T) (≈ S) (≈ R) G.from-cong F.from-cong
    } where module F = Equivalence equiv₁; module G = Equivalence equiv₂

  leftInverse : LeftInverse R S → LeftInverse S T → LeftInverse R T
  leftInverse invˡ₁ invˡ₂ = record
    { to        = G.to ∘ F.to
    ; from      = F.from ∘ G.from
    ; to-cong   = congruent (≈ R) (≈ S) (≈ T) F.to-cong G.to-cong
    ; from-cong = congruent (≈ T) (≈ S) (≈ R) G.from-cong F.from-cong
    ; inverseˡ  = inverseˡ  (≈ R) (≈ S) (≈ T) F.inverseˡ G.inverseˡ
    } where module F = LeftInverse invˡ₁; module G = LeftInverse invˡ₂

  rightInverse : RightInverse R S → RightInverse S T → RightInverse R T
  rightInverse invʳ₁ invʳ₂ = record
    { to        = G.to ∘ F.to
    ; from      = F.from ∘ G.from
    ; to-cong   = congruent (≈ R) (≈ S) (≈ T) F.to-cong G.to-cong
    ; from-cong = congruent (≈ T) (≈ S) (≈ R) G.from-cong F.from-cong
    ; inverseʳ  = inverseʳ  (≈ R) (≈ S) (≈ T) F.inverseʳ G.inverseʳ
    } where module F = RightInverse invʳ₁; module G = RightInverse invʳ₂

  inverse : Inverse R S → Inverse S T → Inverse R T
  inverse inv₁ inv₂ = record
    { to        = G.to ∘ F.to
    ; from      = F.from ∘ G.from
    ; to-cong   = congruent (≈ R) (≈ S) (≈ T) F.to-cong G.to-cong
    ; from-cong = congruent (≈ T) (≈ S) (≈ R) G.from-cong F.from-cong
    ; inverse   = inverseᵇ  (≈ R) (≈ S) (≈ T) F.inverse G.inverse
    } where module F = Inverse inv₁; module G = Inverse inv₂

------------------------------------------------------------------------
-- Propositional bundles

-- Notice the flipped order of the arguments to mirror composition.

infix 8 _⟶-∘_ _↣-∘_ _↠-∘_ _⤖-∘_ _⇔-∘_ _↩-∘_ _↪-∘_ _↔-∘_

_⟶-∘_ : (B ⟶ C) → (A ⟶ B) → (A ⟶ C)
_⟶-∘_ = flip function

_↣-∘_ : B ↣ C → A ↣ B → A ↣ C
_↣-∘_ = flip injection

_↠-∘_ : B ↠ C → A ↠ B → A ↠ C
_↠-∘_ = flip surjection

_⤖-∘_ : B ⤖ C → A ⤖ B → A ⤖ C
_⤖-∘_ = flip bijection

_⇔-∘_ : B ⇔ C → A ⇔ B → A ⇔ C
_⇔-∘_ = flip equivalence

_↩-∘_ : B ↩ C → A ↩ B → A ↩ C
_↩-∘_ = flip leftInverse

_↪-∘_  : B ↪ C → A ↪ B → A ↪ C
_↪-∘_ = flip rightInverse

_↔-∘_ : B ↔ C → A ↔ B → A ↔ C
_↔-∘_ = flip inverse


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version v2.0

infix 8 _∘-⟶_ _∘-↣_ _∘-↠_ _∘-⤖_ _∘-⇔_ _∘-↩_ _∘-↪_ _∘-↔_

_∘-⟶_ = _⟶-∘_
{-# WARNING_ON_USAGE _∘-⟶_
"Warning: _∘-⟶_ was deprecated in v2.0.
Please use _⟶-∘_ instead."
#-}

_∘-↣_ = _↣-∘_
{-# WARNING_ON_USAGE _∘-↣_
"Warning: _∘-↣_ was deprecated in v2.0.
Please use _↣-∘_ instead."
#-}

_∘-↠_ = _↠-∘_
{-# WARNING_ON_USAGE _∘-↠_
"Warning: _∘-↠_ was deprecated in v2.0.
Please use _↠-∘_ instead."
#-}

_∘-⤖_ = _⤖-∘_
{-# WARNING_ON_USAGE _∘-⤖_
"Warning: _∘-⤖_ was deprecated in v2.0.
Please use _⤖-∘_ instead."
#-}

_∘-⇔_ = _⇔-∘_
{-# WARNING_ON_USAGE _∘-⇔_
"Warning: _∘-⇔_ was deprecated in v2.0.
Please use _⇔-∘_ instead."
#-}

_∘-↩_ = _↩-∘_
{-# WARNING_ON_USAGE _∘-↩_
"Warning: _∘-↩_ was deprecated in v2.0.
Please use _↩-∘_ instead."
#-}

_∘-↪_ = _↪-∘_
{-# WARNING_ON_USAGE _∘-↪_
"Warning: _∘-↪_ was deprecated in v2.0.
Please use _↪-∘_ instead."
#-}

_∘-↔_ = _↔-∘_
{-# WARNING_ON_USAGE _∘-↔_
"Warning: _∘-↔_ was deprecated in v2.0.
Please use _↔-∘_ instead."
#-}

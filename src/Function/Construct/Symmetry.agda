------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are symmetric
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Construct.Symmetry where

open import Data.Product.Base using (_,_; swap; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Consequences
  using (module Section)
open import Function.Definitions
  using (Bijective; Injective; Surjective; Inverseˡ; Inverseʳ; Inverseᵇ; Congruent)
open import Function.Structures
  using (IsBijection; IsCongruent; IsRightInverse; IsLeftInverse; IsInverse)
open import Function.Bundles
  using (Bijection; Equivalence; LeftInverse; RightInverse; Inverse; _⤖_; _⇔_; _↩_; _↪_; _↔_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set a

------------------------------------------------------------------------
-- Properties

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) {f : A → B} {f⁻¹ : B → A} where

  inverseʳ : Inverseˡ ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₂ ≈₁ f⁻¹ f
  inverseʳ inv = inv

  inverseˡ : Inverseʳ ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₂ ≈₁ f⁻¹ f
  inverseˡ inv = inv

  inverseᵇ : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₂ ≈₁ f⁻¹ f
  inverseᵇ (invˡ , invʳ) = (invʳ , invˡ)

------------------------------------------------------------------------
-- Structures

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂}
         {f : A → B} (isBij : IsBijection ≈₁ ≈₂ f)
         where

  private module B = IsBijection isBij

  -- We can ALWAYS flip a bijection, WITHOUT knowing the witness produced
  -- by the surjection proof respects the equality on the codomain.
  isBijectionWithoutCongruence : IsBijection ≈₂ ≈₁ B.section
  isBijectionWithoutCongruence = record
    { isInjection = record
      { isCongruent = record
        { cong           = S.cong B.injective B.Eq₁.refl B.Eq₂.sym B.Eq₂.trans
        ; isEquivalence₁ = B.Eq₂.isEquivalence
        ; isEquivalence₂ = B.Eq₁.isEquivalence
        }
      ; injective = S.injective B.Eq₁.refl B.Eq₂.sym B.Eq₂.trans
      }
    ; surjective = S.surjective B.injective B.Eq₁.refl B.Eq₂.trans
    } where module S = Section ≈₂ B.surjective

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {f : A → B} {f⁻¹ : B → A} where

  isCongruent : IsCongruent ≈₁ ≈₂ f → Congruent ≈₂ ≈₁ f⁻¹ → IsCongruent ≈₂ ≈₁ f⁻¹
  isCongruent ic cg = record
    { cong           = cg
    ; isEquivalence₁ = F.isEquivalence₂
    ; isEquivalence₂ = F.isEquivalence₁
    } where module F = IsCongruent ic

  isLeftInverse : IsRightInverse ≈₁ ≈₂ f f⁻¹ → IsLeftInverse ≈₂ ≈₁ f⁻¹ f
  isLeftInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.from-cong
    ; from-cong   = F.to-cong
    ; inverseˡ    = inverseˡ ≈₁ ≈₂ F.inverseʳ
    } where module F = IsRightInverse inv

  isRightInverse : IsLeftInverse ≈₁ ≈₂ f f⁻¹ → IsRightInverse ≈₂ ≈₁ f⁻¹ f
  isRightInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.from-cong
    ; from-cong   = F.to-cong
    ; inverseʳ    = inverseʳ ≈₁ ≈₂ F.inverseˡ
    } where module F = IsLeftInverse inv

  isInverse : IsInverse ≈₁ ≈₂ f f⁻¹ → IsInverse ≈₂ ≈₁ f⁻¹ f
  isInverse f-inv = record
    { isLeftInverse = isLeftInverse F.isRightInverse
    ; inverseʳ      = inverseʳ ≈₁ ≈₂ F.inverseˡ
    } where module F = IsInverse f-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} (bij : Bijection R S) where

  -- We can always flip a bijection WITHOUT knowing if the witness produced
  -- by the surjection proof respects the equality on the codomain.
  bijectionWithoutCongruence : Bijection S R
  bijectionWithoutCongruence = record
    { to        = B.section
    ; cong      = S.cong B.injective B.Eq₁.refl B.Eq₂.sym B.Eq₂.trans
    ; bijective = S.bijective B.injective B.Eq₁.refl B.Eq₂.sym B.Eq₂.trans
    } where module B = Bijection bij ; module S = Section (Setoid._≈_ S) B.surjective

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} where

  equivalence : Equivalence R S → Equivalence S R
  equivalence equiv = record
    { to        = E.from
    ; from      = E.to
    ; to-cong   = E.from-cong
    ; from-cong = E.to-cong
    } where module E = Equivalence equiv

  rightInverse : LeftInverse R S → RightInverse S R
  rightInverse left = record
    { to         = L.from
    ; from       = L.to
    ; to-cong    = L.from-cong
    ; from-cong  = L.to-cong
    ; inverseʳ   = L.inverseˡ
    } where module L = LeftInverse left

  leftInverse : RightInverse R S → LeftInverse S R
  leftInverse right = record
    { to        = R.from
    ; from      = R.to
    ; to-cong   = R.from-cong
    ; from-cong = R.to-cong
    ; inverseˡ  = R.inverseʳ
    } where module R = RightInverse right

  inverse : Inverse R S → Inverse S R
  inverse inv = record
    { to        = I.from
    ; from      = I.to
    ; to-cong   = I.from-cong
    ; from-cong = I.to-cong
    ; inverse   = swap I.inverse
    } where module I = Inverse inv

------------------------------------------------------------------------
-- Propositional bundles

⤖-sym : A ⤖ B → B ⤖ A
⤖-sym = bijectionWithoutCongruence

⇔-sym : A ⇔ B → B ⇔ A
⇔-sym = equivalence

↩-sym : A ↩ B → B ↪ A
↩-sym = rightInverse

↪-sym : A ↪ B → B ↩ A
↪-sym = leftInverse

↔-sym : A ↔ B → B ↔ A
↔-sym = inverse


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

sym-⤖ = ⤖-sym
{-# WARNING_ON_USAGE sym-⤖
"Warning: sym-⤖ was deprecated in v2.0.
Please use ⤖-sym instead."
#-}

sym-⇔ = ⇔-sym
{-# WARNING_ON_USAGE sym-⇔
"Warning: sym-⇔ was deprecated in v2.0.
Please use ⇔-sym instead."
#-}

sym-↩ = ↩-sym
{-# WARNING_ON_USAGE sym-↩
"Warning: sym-↩ was deprecated in v2.0.
Please use ↩-sym instead."
#-}

sym-↪ = ↪-sym
{-# WARNING_ON_USAGE sym-↪
"Warning: sym-↪ was deprecated in v2.0.
Please use ↪-sym instead."
#-}

sym-↔ = ↔-sym
{-# WARNING_ON_USAGE sym-↔
"Warning: sym-↔ was deprecated in v2.0.
Please use ↔-sym instead."
#-}

-- Version 2.3

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {f : A → B}
         ((inj , surj) : Bijective ≈₁ ≈₂ f) (refl : Reflexive ≈₁)
         where

  private
    module S = Section ≈₂ surj

  injective : Symmetric ≈₂ → Transitive ≈₂ →
              Congruent ≈₁ ≈₂ f → Injective ≈₂ ≈₁ S.section
  injective sym trans _ = S.injective refl sym trans

  surjective : Transitive ≈₂ → Surjective ≈₂ ≈₁ S.section
  surjective = S.surjective inj refl

  bijective : Symmetric ≈₂ → Transitive ≈₂ →
              Congruent ≈₁ ≈₂ f → Bijective ≈₂ ≈₁ S.section
  bijective sym trans _ = S.injective refl sym trans , surjective trans
{-# WARNING_ON_USAGE injective
"Warning: injective was deprecated in v2.0.
Please use Function.Consequences.Section.injective instead, with a sharper type."
#-}
{-# WARNING_ON_USAGE surjective
"Warning: surjective was deprecated in v2.0.
Please use Function.Consequences.Section.surjective instead."
#-}
{-# WARNING_ON_USAGE bijective
"Warning: bijective was deprecated in v2.0.
Please use Function.Consequences.Section.bijective instead, with a sharper type."
#-}

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂}
         {f : A → B} (isBij : IsBijection ≈₁ ≈₂ f)
         where
  private module B = IsBijection isBij
  isBijection : Congruent ≈₂ ≈₁ B.section → IsBijection ≈₂ ≈₁ B.section
  isBijection _ = isBijectionWithoutCongruence isBij
{-# WARNING_ON_USAGE isBijection
"Warning: isBijection was deprecated in v2.3.
Please use isBijectionWithoutCongruence instead, with a sharper type."
#-}

module _ {≈₁ : Rel A ℓ₁} {f : A → B} (isBij : IsBijection ≈₁ _≡_ f) where
  isBijection-≡ : IsBijection _≡_ ≈₁ _
  isBijection-≡ = isBijectionWithoutCongruence isBij
{-# WARNING_ON_USAGE isBijection-≡
"Warning: isBijection-≡ was deprecated in v2.3.
Please use isBijectionWithoutCongruence instead, with a sharper type."
#-}

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} (bij : Bijection R S) where
  private module B = Bijection bij
  bijection : Congruent B.Eq₂._≈_ B.Eq₁._≈_ B.section → Bijection S R
  bijection _ = bijectionWithoutCongruence bij

bijection-≡ : {R : Setoid a ℓ₁} {B : Set b} →
              Bijection R (setoid B) → Bijection (setoid B) R
bijection-≡ = bijectionWithoutCongruence
{-# WARNING_ON_USAGE bijection-≡
"Warning: bijection-≡ was deprecated in v2.3.
Please use bijectionWithoutCongruence instead, with a sharper type."
#-}


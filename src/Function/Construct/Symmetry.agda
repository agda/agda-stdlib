------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are symmetric
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Construct.Symmetry where

open import Data.Product.Base using (_,_; swap)
open import Function.Base using (_∘_; id)
open import Function.Definitions
  using (Bijective; Injective; Surjective; Inverseˡ; Inverseʳ; Inverseᵇ
        ; Congruent)
open import Function.Structures
  using (IsBijection; IsCongruent; IsRightInverse; IsLeftInverse; IsInverse)
open import Function.Bundles
  using (Bijection; Equivalence; LeftInverse; RightInverse; Inverse
        ; _⤖_; _⇔_; _↩_; _↪_; _↔_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set a


------------------------------------------------------------------------
-- Properties

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) {f : A → B} {f⁻¹ : B → A} where

  inverseʳ : Inverseˡ ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₂ ≈₁ f⁻¹ f
  inverseʳ = id

  inverseˡ : Inverseʳ ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₂ ≈₁ f⁻¹ f
  inverseˡ = id

  inverseᵇ : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₂ ≈₁ f⁻¹ f
  inverseᵇ = swap

------------------------------------------------------------------------
-- Structures

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {to : A → B}
         (isBij : IsBijection ≈₁ ≈₂ to)
         where

  private module B = IsBijection isBij

  isBijection : IsBijection ≈₂ ≈₁ B.from
  isBijection = record
    { isInjection = record
      { isCongruent = record
        { cong           = B.from-cong
        ; isEquivalence₁ = B.Eq₂.isEquivalence
        ; isEquivalence₂ = B.Eq₁.isEquivalence
        }
      ; injective = B.from-injective
      }
    ; surjective = B.from-surjective
    }

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
    ; inverseˡ    = F.inverseʳ
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
    ; inverseʳ      = F.inverseˡ
    } where module F = IsInverse f-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} where

  bijection : Bijection R S → Bijection S R
  bijection bij = record { IsBijection (isBijection B.isBijection) }
    where module B = Bijection bij

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
⤖-sym = bijection

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

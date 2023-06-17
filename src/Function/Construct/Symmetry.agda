------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are symmetric
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Construct.Symmetry where

open import Data.Product.Base using (_,_; swap; proj₁; proj₂)
open import Function
open import Level using (Level)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set a

------------------------------------------------------------------------
-- Properties

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {f : A → B}
         ((inj , surj) : Bijective ≈₁ ≈₂ f)
         where

  private
    f⁻¹      = proj₁ ∘ surj
    f∘f⁻¹≡id = proj₂ ∘ surj

  injective : Symmetric ≈₂ → Transitive ≈₂ → Congruent ≈₁ ≈₂ f → Injective ≈₂ ≈₁ f⁻¹
  injective sym trans cong gx≈gy = trans (trans (sym (f∘f⁻¹≡id _)) (cong gx≈gy)) (f∘f⁻¹≡id _)

  surjective : Surjective ≈₂ ≈₁ f⁻¹
  surjective x = f x , inj (proj₂ (surj (f x)))

  bijective : Symmetric ≈₂ → Transitive ≈₂ → Congruent ≈₁ ≈₂ f → Bijective ≈₂ ≈₁ f⁻¹
  bijective sym trans cong = injective sym trans cong , surjective

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂)
         (f : A → B) {f⁻¹ : B → A}
         where

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

  private
    module IB = IsBijection isBij
    f⁻¹       = proj₁ ∘ IB.surjective

  -- We can only flip a bijection if the witness produced by the
  -- surjection proof respects the equality on the codomain.
  isBijection : Congruent ≈₂ ≈₁ f⁻¹ → IsBijection ≈₂ ≈₁ f⁻¹
  isBijection f⁻¹-cong = record
    { isInjection = record
      { isCongruent = record
        { cong           = f⁻¹-cong
        ; isEquivalence₁ = IB.Eq₂.isEquivalence
        ; isEquivalence₂ = IB.Eq₁.isEquivalence
        }
      ; injective = injective IB.bijective IB.Eq₂.sym IB.Eq₂.trans IB.cong
      }
    ; surjective = surjective {≈₂ = ≈₂} IB.bijective
    }

module _ {≈₁ : Rel A ℓ₁} {f : A → B} (isBij : IsBijection ≈₁ _≡_ f) where

  -- We can always flip a bijection if using the equality over the
  -- codomain is propositional equality.
  isBijection-≡ : IsBijection _≡_ ≈₁ _
  isBijection-≡ = isBijection isBij (IB.Eq₁.reflexive ∘ cong _)
    where module IB = IsBijection isBij

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂}
         {f : A → B} {f⁻¹ : B → A}
         where

  isCongruent : IsCongruent ≈₁ ≈₂ f → Congruent ≈₂ ≈₁ f⁻¹ → IsCongruent ≈₂ ≈₁ f⁻¹
  isCongruent ic cg = record
    { cong           = cg
    ; isEquivalence₁ = IC.isEquivalence₂
    ; isEquivalence₂ = IC.isEquivalence₁
    } where module IC = IsCongruent ic

  isLeftInverse : IsRightInverse ≈₁ ≈₂ f f⁻¹ → IsLeftInverse ≈₂ ≈₁ f⁻¹ f
  isLeftInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.from-cong
    ; from-cong   = F.cong₁
    ; inverseˡ    = inverseˡ ≈₁ ≈₂ f {f⁻¹} F.inverseʳ
    } where module F = IsRightInverse inv

  isRightInverse : IsLeftInverse ≈₁ ≈₂ f f⁻¹ → IsRightInverse ≈₂ ≈₁ f⁻¹ f
  isRightInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.from-cong
    ; from-cong   = F.to-cong
    ; inverseʳ    = inverseʳ ≈₁ ≈₂ f {f⁻¹} F.inverseˡ
    } where module F = IsLeftInverse inv

  isInverse : IsInverse ≈₁ ≈₂ f f⁻¹ → IsInverse ≈₂ ≈₁ f⁻¹ f
  isInverse f-inv = record
    { isLeftInverse = isLeftInverse F.isRightInverse
    ; inverseʳ      = inverseʳ ≈₁ ≈₂ f F.inverseˡ
    } where module F = IsInverse f-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} (bij : Bijection R S) where

  private
    module IB = Bijection bij
    from      = proj₁ ∘ IB.surjective

  -- We can only flip a bijection if the witness produced by the
  -- surjection proof respects the equality on the codomain.
  bijection : Congruent IB.Eq₂._≈_ IB.Eq₁._≈_ from → Bijection S R
  bijection cong = record
    { to        = from
    ; cong      = cong
    ; bijective = bijective IB.bijective IB.Eq₂.sym IB.Eq₂.trans IB.cong
    }

-- We can always flip a bijection if using the equality over the
-- codomain is propositional equality.
bijection-≡ : {R : Setoid a ℓ₁} {B : Set b} →
              Bijection R (setoid B) → Bijection (setoid B) R
bijection-≡ bij = bijection bij (B.Eq₁.reflexive ∘ cong _)
 where module B = Bijection bij

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
⤖-sym b = bijection b (cong _)

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

-- Version v2.0

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

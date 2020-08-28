------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are symmetric
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Construct.Symmetry where

open import Data.Product using (_,_; swap)
open import Function
open import Level using (Level)
open import Relation.Binary hiding (_⇔_)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Properties

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
         {f : A → B} {f⁻¹ : B → A}
         where

  isCongruent : IsCongruent ≈₁ ≈₂ f → Congruent ≈₂ ≈₁ f⁻¹ → IsCongruent ≈₂ ≈₁ f⁻¹
  isCongruent ic cg = record
    { cong = cg
    ; isEquivalence₁ = IC.isEquivalence₂
    ; isEquivalence₂ = IC.isEquivalence₁
    }
    where module IC = IsCongruent ic

  isLeftInverse : IsRightInverse ≈₁ ≈₂ f f⁻¹ → IsLeftInverse ≈₂ ≈₁ f⁻¹ f
  isLeftInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.cong₂
    ; cong₂ = F.cong₁
    ; inverseˡ = inverseˡ ≈₁ ≈₂ f {f⁻¹} F.inverseʳ
    }
    where module F = IsRightInverse inv

  isRightInverse : IsLeftInverse ≈₁ ≈₂ f f⁻¹ → IsRightInverse ≈₂ ≈₁ f⁻¹ f
  isRightInverse inv = record
    { isCongruent = isCongruent F.isCongruent F.cong₂
    ; cong₂ = F.cong₁
    ; inverseʳ = inverseʳ ≈₁ ≈₂ f {f⁻¹} F.inverseˡ
    }
    where module F = IsLeftInverse inv

  isInverse : IsInverse ≈₁ ≈₂ f f⁻¹ → IsInverse ≈₂ ≈₁ f⁻¹ f
  isInverse f-inv = record
    { isLeftInverse = isLeftInverse F.isRightInverse
    ; inverseʳ = inverseʳ ≈₁ ≈₂ f F.inverseˡ
    }
    where module F = IsInverse f-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} where

  equivalence : Equivalence R S → Equivalence S R
  equivalence equiv = record
    { f = E.g
    ; g = E.f
    ; cong₁ = E.cong₂
    ; cong₂ = E.cong₁
    }
    where module E = Equivalence equiv

  rightInverse : LeftInverse R S → RightInverse S R
  rightInverse left = record
    { f = L.g
    ; g = L.f
    ; cong₁ = L.cong₂
    ; cong₂ = L.cong₁
    ; inverseʳ = L.inverseˡ
    } where module L = LeftInverse left

  leftInverse : RightInverse R S → LeftInverse S R
  leftInverse right = record
    { f = R.g
    ; g = R.f
    ; cong₁ = R.cong₂
    ; cong₂ = R.cong₁
    ; inverseˡ = R.inverseʳ
    } where module R = RightInverse right

  inverse : Inverse R S → Inverse S R
  inverse inv = record
    { f = I.f⁻¹
    ; f⁻¹ = I.f
    ; cong₁ = I.cong₂
    ; cong₂ = I.cong₁
    ; inverse = swap I.inverse
    } where module I = Inverse inv

------------------------------------------------------------------------
-- Propositional bundles

sym-⇔ : A ⇔ B → B ⇔ A
sym-⇔ = equivalence

sym-↩ : A ↩ B → B ↪ A
sym-↩ = rightInverse

sym-↪ : A ↪ B → B ↩ A
sym-↪ = leftInverse

sym-↔ : A ↔ B → B ↔ A
sym-↔ = inverse

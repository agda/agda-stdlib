------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient rings
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup; Ring)
open import Algebra.Construct.Sub.Ring.Ideal using (Ideal)
import Algebra.Construct.Quotient.AbelianGroup as Quotient

module Algebra.Construct.Quotient.Ring
  {c ℓ} (R : Ring c ℓ) {c′ ℓ′} (I : Ideal R c′ ℓ′)
  where

open import Algebra.Definitions using (Congruent₂)
open import Algebra.Morphism.Structures using (IsRingHomomorphism)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Level using (_⊔_)

private
  module R = Ring R
  module I = Ideal I
  module R/I = Quotient R.+-abelianGroup I.subgroup


open R/I public
  using (_≋_; _by_; ≈⇒≋; π; π-isMonoidHomomorphism; π-surjective)
  renaming (abelianGroup to +-abelianGroup)

*-cong : Congruent₂ _≋_ R._*_
*-cong {x} {y} {u} {v} (j by ιj+x≈y) (k by ιk+u≈v) =
  ι j *ₗ k +ᴹ j *ᵣ u +ᴹ x *ₗ k by begin
  ι (ι j *ₗ k +ᴹ j *ᵣ u +ᴹ x *ₗ k) + x * u       ≈⟨ +-congʳ (ι.+ᴹ-homo (ι j *ₗ k +ᴹ j *ᵣ u) (x *ₗ k)) ⟩
  ι (ι j *ₗ k +ᴹ j *ᵣ u) + ι (x *ₗ k) + x * u    ≈⟨ +-congʳ (+-congʳ (ι.+ᴹ-homo (ι j *ₗ k) (j *ᵣ u))) ⟩
  ι (ι j *ₗ k) + ι (j *ᵣ u) + ι (x *ₗ k) + x * u ≈⟨ +-congʳ (+-cong (+-cong (ι.*ₗ-homo (ι j) k) (ι.*ᵣ-homo u j)) (ι.*ₗ-homo x k)) ⟩
  ι j * ι k + ι j * u + x * ι k + x * u          ≈⟨ binomial-expansion (ι j) x (ι k) u ⟨
  (ι j + x) * (ι k + u)                          ≈⟨ R.*-cong ιj+x≈y ιk+u≈v ⟩
  y * v                                          ∎
  where
  open R using (_+_; _*_; +-congʳ ;+-cong)
  open import Algebra.Properties.Semiring R.semiring using (binomial-expansion)
  open import Relation.Binary.Reasoning.Setoid R.setoid
  open I using (ι; _*ₗ_; _*ᵣ_; _+ᴹ_)

ring : Ring c (c ⊔ ℓ ⊔ c′)
ring = record
  { isRing = record
    { +-isAbelianGroup = isAbelianGroup
    ; *-cong = *-cong
    ; *-assoc = λ x y z → ≈⇒≋ (R.*-assoc x y z)
    ; *-identity = ≈⇒≋ ∘ R.*-identityˡ , ≈⇒≋ ∘ R.*-identityʳ
    ; distrib = (λ x y z → ≈⇒≋ (R.distribˡ x y z)) , (λ x y z → ≈⇒≋ (R.distribʳ x y z))
    }
  } where open AbelianGroup +-abelianGroup using (isAbelianGroup)

private module Q = Ring ring

-- Public re-exports

_/_ : Ring c (c ⊔ ℓ ⊔ c′)
_/_ = ring

π-isRingHomomorphism : IsRingHomomorphism R.rawRing Q.rawRing π
π-isRingHomomorphism = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = π-isMonoidHomomorphism
      ; *-homo = λ _ _ → Q.refl
      }
    ; 1#-homo = Q.refl
    }
  ; -‿homo = λ _ → Q.refl
  }


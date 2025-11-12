------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient of a Ring by an Ideal
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup; Ring; RawRing)
open import Algebra.Construct.Sub.Ring.Ideal using (Ideal)

module Algebra.Construct.Quotient.Ring
  {c ℓ} (R : Ring c ℓ) {c′ ℓ′} (I : Ideal R c′ ℓ′)
  where

open import Algebra.Morphism.Structures using (IsRingHomomorphism)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Level using (_⊔_)

import Algebra.Construct.Quotient.AbelianGroup as Quotient

private
  module R = Ring R
  module I = Ideal I
  module R/I = Quotient R.+-abelianGroup I.subgroup


open R/I public
  using (_≋_; _by_; ≋-refl; ≈⇒≋
        ; quotientAbelianGroup
        ; π; π-isMonoidHomomorphism; π-surjective
        )

open import Algebra.Definitions _≋_ using (Congruent₂)

≋-*-cong : Congruent₂ R._*_
≋-*-cong {x} {y} {u} {v} (j by ιj+x≈y) (k by ιk+u≈v) = ι j *ₗ k +ᴹ j *ᵣ u +ᴹ x *ₗ k by begin
  ι (ι j *ₗ k +ᴹ j *ᵣ u +ᴹ x *ₗ k) + x * u       ≈⟨ +-congʳ (ι.+ᴹ-homo (ι j *ₗ k +ᴹ j *ᵣ u) (x *ₗ k)) ⟩
  ι (ι j *ₗ k +ᴹ j *ᵣ u) + ι (x *ₗ k) + x * u    ≈⟨ +-congʳ (+-congʳ (ι.+ᴹ-homo (ι j *ₗ k) (j *ᵣ u))) ⟩
  ι (ι j *ₗ k) + ι (j *ᵣ u) + ι (x *ₗ k) + x * u ≈⟨ +-congʳ (+-cong (+-cong (ι.*ₗ-homo (ι j) k) (ι.*ᵣ-homo u j)) (ι.*ₗ-homo x k)) ⟩
  ι j * ι k + ι j * u + x * ι k + x * u          ≈⟨ binomial-expansion (ι j) x (ι k) u ⟨
  (ι j + x) * (ι k + u)                          ≈⟨ *-cong ιj+x≈y ιk+u≈v ⟩
  y * v                                          ∎
  where
  open R using (_+_; _*_; +-congʳ ;+-cong; *-cong)
  open import Algebra.Properties.Semiring R.semiring using (binomial-expansion)
  open import Relation.Binary.Reasoning.Setoid R.setoid
  open I using (ι; _*ₗ_; _*ᵣ_; _+ᴹ_)

quotientRawRing : RawRing c (c ⊔ ℓ ⊔ c′)
quotientRawRing = record { RawRing R.rawRing hiding (_≈_) ; _≈_ = _≋_ }

quotientRing : Ring c (c ⊔ ℓ ⊔ c′)
quotientRing = record
  { isRing = record
    { +-isAbelianGroup = isAbelianGroup
    ; *-cong = ≋-*-cong
    ; *-assoc = λ x y z → ≈⇒≋ (R.*-assoc x y z)
    ; *-identity = ≈⇒≋ ∘ R.*-identityˡ , ≈⇒≋ ∘ R.*-identityʳ
    ; distrib = (λ x y z → ≈⇒≋ (R.distribˡ x y z)) , (λ x y z → ≈⇒≋ (R.distribʳ x y z))
    }
  } where open AbelianGroup quotientAbelianGroup using (isAbelianGroup)

π-isRingHomomorphism : IsRingHomomorphism R.rawRing quotientRawRing π
π-isRingHomomorphism = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = π-isMonoidHomomorphism
      ; *-homo = λ _ _ → ≋-refl
      }
    ; 1#-homo = ≋-refl
    }
  ; -‿homo = λ _ → ≋-refl
  }


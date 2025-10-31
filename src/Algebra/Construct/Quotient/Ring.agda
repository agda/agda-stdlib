------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient rings
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Ring; RawRing)
open import Algebra.Ideal using (Ideal)

module Algebra.Construct.Quotient.Ring {c ℓ} (R : Ring c ℓ) {c′ ℓ′} (I : Ideal R c′ ℓ′) where

open Ring R
private module I = Ideal I
open I using (ι; normalSubgroup)

open import Algebra.Construct.Quotient.Group +-group normalSubgroup public
  using (_≋_; _by_; ≋-refl; ≋-sym; ≋-trans; ≋-isEquivalence; ≈⇒≋; quotientIsGroup; quotientGroup; π; π-surjective)
  renaming (≋-∙-cong to ≋-+-cong; ≋-⁻¹-cong to ≋‿-‿cong)

open import Algebra.Definitions _≋_
open import Algebra.Morphism.Structures using (IsRingHomomorphism)
open import Algebra.Properties.Semiring semiring
open import Algebra.Properties.Ring R
open import Algebra.Structures
open import Function.Definitions using (Surjective)
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

≋-*-cong : Congruent₂ _*_
≋-*-cong {x} {y} {u} {v} (j by ιj+x≈y) (k by ιk+u≈v) = ι j I.*ₗ k I.+ᴹ j I.*ᵣ u I.+ᴹ x I.*ₗ k by begin
  ι (ι j I.*ₗ k I.+ᴹ j I.*ᵣ u I.+ᴹ x I.*ₗ k) + x * u   ≈⟨ +-congʳ (ι.+ᴹ-homo (ι j I.*ₗ k I.+ᴹ j I.*ᵣ u) (x I.*ₗ k)) ⟩
  ι (ι j I.*ₗ k I.+ᴹ j I.*ᵣ u) + ι (x I.*ₗ k) + x * u  ≈⟨ +-congʳ (+-congʳ (ι.+ᴹ-homo (ι j I.*ₗ k) (j I.*ᵣ u))) ⟩
  ι (ι j I.*ₗ k) + ι (j I.*ᵣ u) + ι (x I.*ₗ k) + x * u ≈⟨ +-congʳ (+-cong (+-cong (ι.*ₗ-homo (ι j) k) (ι.*ᵣ-homo u j)) (ι.*ₗ-homo x k)) ⟩
  ι j * ι k + ι j * u + x * ι k + x * u                ≈⟨ binomial-expansion (ι j) x (ι k) u ⟨
  (ι j + x) * (ι k + u)                                ≈⟨ *-cong ιj+x≈y ιk+u≈v ⟩
  y * v                                                ∎

quotientRawRing : RawRing c (c ⊔ ℓ ⊔ c′)
quotientRawRing = record
  { Carrier = Carrier
  ; _≈_ = _≋_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0#
  ; 1# = 1#
  }

quotientIsRing : IsRing _≋_ _+_ _*_ (-_) 0# 1#
quotientIsRing = record
  { +-isAbelianGroup = record
    { isGroup = quotientIsGroup
    ; comm = λ x y → ≈⇒≋ (+-comm x y)
    }
  ; *-cong = ≋-*-cong
  ; *-assoc = λ x y z → ≈⇒≋ (*-assoc x y z)
  ; *-identity = record
    { fst = λ x → ≈⇒≋ (*-identityˡ x)
    ; snd = λ x → ≈⇒≋ (*-identityʳ x)
    }
  ; distrib = record
    { fst = λ x y z → ≈⇒≋ (distribˡ x y z)
    ; snd = λ x y z → ≈⇒≋ (distribʳ x y z)
    }
  }

quotientRing : Ring c (c ⊔ ℓ ⊔ c′)
quotientRing = record { isRing = quotientIsRing }

π-isHomomorphism : IsRingHomomorphism rawRing quotientRawRing π
π-isHomomorphism = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record
            { cong = ≈⇒≋
            }
          ; homo = λ _ _ → ≋-refl
          }
        ; ε-homo = ≋-refl
        }
      ; *-homo = λ _ _ → ≋-refl
      }
    ; 1#-homo = ≋-refl
    }
  ; -‿homo = λ _ → ≋-refl
  }

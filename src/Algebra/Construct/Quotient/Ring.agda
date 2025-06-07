------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient rings
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Ring)
open import Algebra.Ideal using (Ideal)

module Algebra.Construct.Quotient.Ring {c ℓ c′ ℓ′} (R : Ring c ℓ) (I : Ideal R c′ ℓ′) where

open Ring R
open Ideal I

open import Algebra.Construct.Quotient.Group +-group normalSubgroup
  public
  using (_≋_; _by_; ≋-refl; ≋-sym; ≋-trans; ≋-isEquivalence; ≈⇒≋; quotientIsGroup; quotientGroup)
  renaming (≋-∙-cong to ≋-+-cong; ≋-⁻¹-cong to ≋‿-‿cong)

open import Algebra.Definitions _≋_
open import Algebra.Properties.Ring R
open import Algebra.Structures
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

≋-*-cong : Congruent₂ _*_
≋-*-cong {x} {y} {u} {v} (j by x-y≈ιj) (k by u-v≈ιk) = j I.*ᵣ u I.+ᴹ y I.*ₗ k by begin
    x * u - y * v                       ≈⟨ +-congʳ (+-identityʳ (x * u)) ⟨
    x * u + 0# - y * v                  ≈⟨ +-congʳ (+-congˡ (-‿inverseˡ (y * u))) ⟨
    x * u + (- (y * u) + y * u) - y * v ≈⟨ +-congʳ (+-assoc (x * u) (- (y * u)) (y * u)) ⟨
    ((x * u - y * u) + y * u) - y * v   ≈⟨ +-assoc (x * u - y * u) (y * u) (- (y * v)) ⟩
    (x * u - y * u) + (y * u - y * v)   ≈⟨ +-cong ([y-z]x≈yx-zx u x y) (x[y-z]≈xy-xz y u v) ⟨
    (x - y) * u + y * (u - v)           ≈⟨ +-cong (*-congʳ x-y≈ιj) (*-congˡ u-v≈ιk) ⟩
    ι j * u + y * ι k                   ≈⟨ +-cong (ι.*ᵣ-homo u j) (ι.*ₗ-homo y k) ⟨
    ι (j I.*ᵣ u) + ι (y I.*ₗ k)         ≈⟨ ι.+ᴹ-homo (j I.*ᵣ u) (y I.*ₗ k) ⟨
    ι (j I.*ᵣ u I.+ᴹ y I.*ₗ k)          ∎

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

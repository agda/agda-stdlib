------------------------------------------------------------------------
-- The Agda standard library
--
-- Half adjoint equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.HalfAdjointEquivalence where

open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Level
open import Relation.Binary.PropositionalEquality

-- Half adjoint equivalences (see the HoTT book).

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to               : A → B
    from             : B → A
    left-inverse-of  : ∀ x → from (to x) ≡ x
    right-inverse-of : ∀ x → to (from x) ≡ x
    left-right       :
      ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)

  -- Half adjoint equivalences can be turned into inverses.

  inverse : A ↔ B
  inverse = Inv.inverse to from left-inverse-of right-inverse-of

  -- The forward direction of a half adjoint equivalence is injective.

  injective : ∀ {x y} → to x ≡ to y → x ≡ y
  injective {x} {y} to-x≡to-y =
    x            ≡⟨ sym (left-inverse-of _) ⟩
    from (to x)  ≡⟨ cong from to-x≡to-y ⟩
    from (to y)  ≡⟨ left-inverse-of _ ⟩
    y            ∎
    where
    open ≡-Reasoning

-- Inverses can be turned into half adjoint equivalences.
--
-- (This proof is based on one in the HoTT book.)

↔→≃ : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → A ≃ B
↔→≃ A↔B = record
  { to               = to   ⟨$⟩_
  ; from             = from ⟨$⟩_
  ; left-inverse-of  = left-inverse-of
  ; right-inverse-of = right-inverse-of
  ; left-right       = left-right
  }
  where
  open ≡-Reasoning
  open module A↔B = Inverse A↔B using (to; from; left-inverse-of)

  right-inverse-of : ∀ x → to ⟨$⟩ (from ⟨$⟩ x) ≡ x
  right-inverse-of x =
    to ⟨$⟩ (from ⟨$⟩ x)                      ≡⟨ sym (A↔B.right-inverse-of _) ⟩
    to ⟨$⟩ (from ⟨$⟩ (to ⟨$⟩ (from ⟨$⟩ x)))  ≡⟨ cong (to ⟨$⟩_) (left-inverse-of _) ⟩
    to ⟨$⟩ (from ⟨$⟩ x)                      ≡⟨ A↔B.right-inverse-of _ ⟩
    x                                        ∎

  left-right :
    ∀ x →
    cong (to ⟨$⟩_) (left-inverse-of x) ≡ right-inverse-of (to ⟨$⟩ x)
  left-right x =
    cong (to ⟨$⟩_) (left-inverse-of x)               ≡⟨⟩

    trans refl (cong (to ⟨$⟩_) (left-inverse-of _))  ≡⟨ cong (λ p → trans p (cong (to ⟨$⟩_) _))
                                                          (sym (trans-symˡ (A↔B.right-inverse-of _))) ⟩
    trans (trans (sym (A↔B.right-inverse-of _))
               (A↔B.right-inverse-of _))
      (cong (to ⟨$⟩_) (left-inverse-of _))           ≡⟨ trans-assoc (sym (A↔B.right-inverse-of _)) ⟩

    trans (sym (A↔B.right-inverse-of _))
      (trans (A↔B.right-inverse-of _)
         (cong (to ⟨$⟩_) (left-inverse-of _)))       ≡⟨ cong (trans (sym (A↔B.right-inverse-of _))) lemma ⟩

    trans (sym (A↔B.right-inverse-of _))
      (trans (cong (to ⟨$⟩_) (left-inverse-of _))
         (trans (A↔B.right-inverse-of _) refl))      ≡⟨⟩

    right-inverse-of (to ⟨$⟩ x)                      ∎
    where
    lemma =
      trans (A↔B.right-inverse-of _)
        (cong (to ⟨$⟩_) (left-inverse-of _))             ≡⟨ cong (trans (A↔B.right-inverse-of _)) (sym (cong-id _)) ⟩

      trans (A↔B.right-inverse-of _)
        (cong id (cong (to ⟨$⟩_) (left-inverse-of _)))   ≡⟨ sym (naturality A↔B.right-inverse-of) ⟩

      trans (cong ((to ⟨$⟩_) ∘ (from ⟨$⟩_))
                 (cong (to ⟨$⟩_) (left-inverse-of _)))
        (A↔B.right-inverse-of _)                         ≡⟨ cong (λ p → trans p (A↔B.right-inverse-of _))
                                                              (sym (cong-∘ _)) ⟩
      trans (cong ((to ⟨$⟩_) ∘ (from ⟨$⟩_) ∘ (to ⟨$⟩_))
                      (left-inverse-of _))
        (A↔B.right-inverse-of _)                         ≡⟨ cong (λ p → trans p (A↔B.right-inverse-of _))
                                                              (cong-∘ _) ⟩
      trans (cong (to ⟨$⟩_)
                 (cong ((from ⟨$⟩_) ∘ (to ⟨$⟩_))
                    (left-inverse-of _)))
        (A↔B.right-inverse-of _)                         ≡⟨ cong (λ p → trans (cong (to ⟨$⟩_) p) _)
                                                              (cong-≡id left-inverse-of) ⟩
      trans (cong (to ⟨$⟩_) (left-inverse-of _))
        (A↔B.right-inverse-of _)                         ≡⟨ cong (trans (cong (to ⟨$⟩_) (left-inverse-of _)))
                                                              (sym (trans-reflʳ _)) ⟩
      trans (cong (to ⟨$⟩_) (left-inverse-of _))
        (trans (A↔B.right-inverse-of _) refl)            ∎

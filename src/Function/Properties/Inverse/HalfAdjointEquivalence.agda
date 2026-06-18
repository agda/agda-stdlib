------------------------------------------------------------------------
-- The Agda standard library
--
-- Half adjoint equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Inverse.HalfAdjointEquivalence where

open import Function.Base using (id; _∘_)
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; trans-reflʳ; cong-≡id; cong-∘; naturality
        ; cong-id; trans-assoc; trans-symˡ; module ≡-Reasoning)

private
  variable
    a b : Level
    A B : Set a

-- Half adjoint equivalences (see the HoTT book).
--
-- They are inverses with an extra coherence condition that the left
-- and right inversion proofs interact the right way with `cong`.

infix 4 _≃_

record _≃_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to               : A → B
    from             : B → A
    left-inverse-of  : ∀ x → from (to x) ≡ x
    right-inverse-of : ∀ x → to (from x) ≡ x
    left-right       : ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)

  -- The forward direction of a half adjoint equivalence is injective.

  injective : ∀ {x y} → to x ≡ to y → x ≡ y
  injective {x} {y} to-x≡to-y =
    x            ≡⟨ sym (left-inverse-of _) ⟩
    from (to x)  ≡⟨ cong from to-x≡to-y ⟩
    from (to y)  ≡⟨ left-inverse-of _ ⟩
    y            ∎
    where open ≡-Reasoning

-- Half adjoint equivalences can be turned into inverses.

≃⇒↔ : A ≃ B → A ↔ B
≃⇒↔ A≃B = mk↔ₛ′ to from right-inverse-of left-inverse-of
  where open _≃_ A≃B

-- Inverses can be turned into half adjoint equivalences.
--
-- (This proof is based on one in the HoTT book.)

↔⇒≃ : A ↔ B → A ≃ B
↔⇒≃ A↔B = record
  { to               = to
  ; from             = from
  ; left-inverse-of  = strictlyInverseʳ
  ; right-inverse-of = right-inverse-of
  ; left-right       = left-right
  }
  where
  open ≡-Reasoning
  open module A↔B = Inverse A↔B

  right-inverse-of : ∀ x → to (from x) ≡ x
  right-inverse-of x =
    to (from x)               ≡⟨ sym (A↔B.strictlyInverseˡ _) ⟩
    to (from (to (from x)))   ≡⟨ cong to (strictlyInverseʳ  _) ⟩
    to (from x)               ≡⟨ A↔B.strictlyInverseˡ _ ⟩
    x                         ∎

  left-right :
    ∀ x →
    cong to (strictlyInverseʳ x) ≡ right-inverse-of (to x)
  left-right x =
    cong to (strictlyInverseʳ x)               ≡⟨⟩

    trans refl (cong to (strictlyInverseʳ _))  ≡⟨ cong (λ p → trans p (cong to (strictlyInverseʳ _)))
                                                          (sym (trans-symˡ (A↔B.strictlyInverseˡ _))) ⟩
    trans (trans (sym (A↔B.strictlyInverseˡ _))
               (A↔B.strictlyInverseˡ _))
      (cong to (strictlyInverseʳ _))           ≡⟨ trans-assoc (sym (A↔B.strictlyInverseˡ _)) ⟩

    trans (sym (A↔B.strictlyInverseˡ _))
      (trans (A↔B.strictlyInverseˡ _)
         (cong to (strictlyInverseʳ _)))       ≡⟨ cong (trans (sym (A↔B.strictlyInverseˡ _))) lemma ⟩

    trans (sym (A↔B.strictlyInverseˡ _))
      (trans (cong to (strictlyInverseʳ _))
         (trans (A↔B.strictlyInverseˡ _) refl))      ≡⟨⟩

    right-inverse-of (to x)                      ∎
    where
    lemma =
      trans (A↔B.strictlyInverseˡ _)
        (cong to (strictlyInverseʳ _))             ≡⟨ cong (trans (A↔B.strictlyInverseˡ _)) (sym (cong-id _)) ⟩

      trans (A↔B.strictlyInverseˡ _)
        (cong id (cong to (strictlyInverseʳ _)))   ≡⟨ sym (naturality A↔B.strictlyInverseˡ) ⟩

      trans (cong (to ∘ from)
                 (cong to (strictlyInverseʳ _)))
        (A↔B.strictlyInverseˡ _)                         ≡⟨ cong (λ p → trans p (A↔B.strictlyInverseˡ _))
                                                              (sym (cong-∘ _)) ⟩
      trans (cong (to ∘ from ∘ to)
                      (strictlyInverseʳ _))
        (A↔B.strictlyInverseˡ _)                         ≡⟨ cong (λ p → trans p (A↔B.strictlyInverseˡ _))
                                                              (cong-∘ _) ⟩
      trans (cong to
                 (cong (from ∘ to)
                    (strictlyInverseʳ _)))
        (A↔B.strictlyInverseˡ _)                         ≡⟨ cong (λ p → trans (cong to p) (strictlyInverseˡ (to x)))
                                                              (cong-≡id strictlyInverseʳ) ⟩
      trans (cong to (strictlyInverseʳ _))
        (A↔B.strictlyInverseˡ _)                         ≡⟨ cong (trans (cong to (strictlyInverseʳ _)))
                                                              (sym (trans-reflʳ _)) ⟩
      trans (cong to (strictlyInverseʳ _))
        (trans (A↔B.strictlyInverseˡ _) refl)            ∎

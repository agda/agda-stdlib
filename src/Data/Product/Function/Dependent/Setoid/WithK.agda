




------------------------------------------------------------------------
-- Properties related to "relatedness"

module _ {a₁ a₂ b₁ b₁′ b₂ b₂′} {A₁ : Set a₁} {A₂ : Set a₂} where

  inverse : {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′) →
    (A₁↔A₂ : A₁ ↔ A₂) →
    (∀ {x} → Inverse (B₁ atₛ x) (B₂ atₛ (Inverse.to A₁↔A₂ ⟨$⟩ x))) →
    Inverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  inverse {B₁} B₂ A₁↔A₂ B₁↔B₂ = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = left
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    surj = surjection B₂ (Inverse.surjection A₁↔A₂)
                         (Inverse.surjection B₁↔B₂)

    left : Surjection.from surj LeftInverseOf Surjection.to surj
    left (x , y) =
      Inverse.left-inverse-of A₁↔A₂ x ,
      IndexedSetoid.trans B₁
        (lemma (P.sym (Inverse.left-inverse-of A₁↔A₂ x))
               (P.sym (Inverse.right-inverse-of A₁↔A₂
                       (Inverse.to A₁↔A₂ ⟨$⟩ x))))
        (Inverse.left-inverse-of B₁↔B₂ y)
      where
      lemma :
        ∀ {x x′ y} → x ≡ x′ →
        (eq : (Inverse.to A₁↔A₂ ⟨$⟩ x) ≡ (Inverse.to A₁↔A₂ ⟨$⟩ x′)) →
        IndexedSetoid._≈_ B₁
          (Inverse.from B₁↔B₂ ⟨$⟩ P.subst (IndexedSetoid.Carrier B₂) eq y)
          (Inverse.from B₁↔B₂ ⟨$⟩ y)
      lemma P.refl P.refl = IndexedSetoid.refl B₁

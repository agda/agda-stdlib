------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties that are related to pointwise lifting of binary
-- relations to sigma types and make use of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Relation.Binary.Pointwise.Dependent.WithK where

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.Dependent hiding (↣; ↔)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection as Inj using (_↣_; module Injection)
open import Function.Inverse as Inv using (Inverse; _↔_)
open import Function.LeftInverse using (_LeftInverseOf_)
open import Function.Surjection using (Surjection)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Pointwise

module _ {a b} {A : Set a} {B : A → Set b} where

  Pointwise-≡⇒≡ : Pointwise B _≡_ (λ x y → x ≅ y) ⇒ _≡_
  Pointwise-≡⇒≡ (P.refl , H.refl) = P.refl

  ≡⇒Pointwise-≡ : _≡_ ⇒ Pointwise B _≡_ (λ x y → x ≅ y)
  ≡⇒Pointwise-≡ P.refl = (P.refl , H.refl)

  Pointwise-≡↔≡ : Inverse (setoid (P.setoid A) (H.indexedSetoid B))
                  (P.setoid (Σ A B))
  Pointwise-≡↔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
    ; inverse-of = record
      { left-inverse-of  = uncurry (λ _ _ → (P.refl , H.refl))
      ; right-inverse-of = λ _ → P.refl
      }
    }

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

------------------------------------------------------------------------

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {b₁ b₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
         where

  ↣ : ∀ (A₁↣A₂ : A₁ ↣ A₂) →
      (∀ {x} → B₁ x ↣ B₂ (Injection.to A₁↣A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↣ Σ A₂ B₂
  ↣ A₁↣A₂ B₁↣B₂ =
    Inverse.injection Pointwise-≡↔≡ ⟨∘⟩
    injection (H.indexedSetoid B₂) A₁↣A₂
      (Inverse.injection (H.≡↔≅ B₂) ⟨∘⟩
       B₁↣B₂ ⟨∘⟩
       Inverse.injection (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

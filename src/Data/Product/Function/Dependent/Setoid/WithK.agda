------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Function.Dependent.Setoid.WithK where

open import Data.Product
open import Data.Product.Function.Dependent.Setoid using (surjection)
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Relation.Binary
open import Function.Core
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; Injective; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; _LeftInverseOf_; _RightInverseOf_; module LeftInverse)
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Relation.Binary as B
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Combinator for Inverse

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

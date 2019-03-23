------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning uniqueness of identity proofs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Axiom.UniquenessOfIdentityProofs where

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core

------------------------------------------------------------------------
-- Definition
--
-- Uniqueness of Identity Proofs (UIP) states that all proofs of
-- equality are themselves equal. In other words, the equality relation
-- is irrelevant. Here we define UIP relative to a given type.

UIP : ∀ {a} (A : Set a) → Set a
UIP A = Irrelevant {A = A} _≡_

------------------------------------------------------------------------
-- Properties

-- UIP always holds when using axiom K
-- (see `Axiom.UniquenessOfIdentityProofs.WithK`).

-- The existence of a constant function over proofs of equality for
-- elements in A is enough to prove UIP for A. Indeed, we can relate any
-- proof to its image via this function which we then know is equal to
-- the image of any other proof.

module Constant⇒UIP
  {a} {A : Set a} (f : _≡_ {A = A} ⇒ _≡_)
  (f-constant : ∀ {a b} (p q : a ≡ b) → f p ≡ f q)
  where

  ≡-canonical : ∀ {a b} (p : a ≡ b) → trans (sym (f refl)) (f p) ≡ p
  ≡-canonical refl = trans-symˡ (f refl)

  ≡-irrelevant : UIP A
  ≡-irrelevant p q = begin
    p                          ≡⟨ sym (≡-canonical p) ⟩
    trans (sym (f refl)) (f p) ≡⟨ cong (trans _) (f-constant p q) ⟩
    trans (sym (f refl)) (f q) ≡⟨ ≡-canonical q ⟩
    q                          ∎ where open ≡-Reasoning

-- If equality is decidable for a given type, then we can prove UIP for
-- that type. Indeed, the decision procedure allows us to define a
-- function over proofs of equality which is constant: it returns the
-- proof produced by the decision procedure.

module Decidable⇒UIP
  {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A}))
  where

  ≡-normalise : _≡_ {A = A} ⇒ _≡_
  ≡-normalise {a} {b} a≡b with a ≟ b
  ... | yes p = p
  ... | no ¬p = ⊥-elim (¬p a≡b)

  ≡-normalise-constant : ∀ {a b} (p q : a ≡ b) → ≡-normalise p ≡ ≡-normalise q
  ≡-normalise-constant {a} {b} p q with a ≟ b
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  ≡-irrelevant : UIP A
  ≡-irrelevant = Constant⇒UIP.≡-irrelevant ≡-normalise ≡-normalise-constant

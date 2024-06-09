------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning uniqueness of identity proofs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Axiom.UniquenessOfIdentityProofs where

open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (recompute; recompute-constant)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

private
  variable
    a : Level
    A : Set a
    x y : A

------------------------------------------------------------------------
-- Definition
--
-- Uniqueness of Identity Proofs (UIP) states that all proofs of
-- equality are themselves equal. In other words, the equality relation
-- is irrelevant. Here we define UIP relative to a given type.

UIP : (A : Set a) → Set a
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
  (f : _≡_ {A = A} ⇒ _≡_)
  (f-constant : ∀ {x y} (p q : x ≡ y) → f p ≡ f q)
  where

  ≡-canonical : (p : x ≡ y) → trans (sym (f refl)) (f p) ≡ p
  ≡-canonical refl = trans-symˡ (f refl)

  ≡-irrelevant : UIP A
  ≡-irrelevant p q = begin
    p                          ≡⟨ sym (≡-canonical p) ⟩
    trans (sym (f refl)) (f p) ≡⟨ cong (trans _) (f-constant p q) ⟩
    trans (sym (f refl)) (f q) ≡⟨ ≡-canonical q ⟩
    q                          ∎
    where open ≡-Reasoning

-- If equality is decidable for a given type, then we can prove UIP for
-- that type. Indeed, the decision procedure allows us to define a
-- function over proofs of equality which is constant: it returns the
-- proof produced by the decision procedure.

module Decidable⇒UIP (_≟_ : DecidableEquality A)
  where

  ≡-normalise : _≡_ {A = A} ⇒ _≡_
  ≡-normalise {x} {y} x≡y = recompute (x ≟ y) x≡y

  ≡-normalise-constant : (p q : x ≡ y) → ≡-normalise p ≡ ≡-normalise q
  ≡-normalise-constant {x = x} {y = y} = recompute-constant (x ≟ y)

  ≡-irrelevant : UIP A
  ≡-irrelevant = Constant⇒UIP.≡-irrelevant ≡-normalise ≡-normalise-constant

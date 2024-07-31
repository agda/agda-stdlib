------------------------------------------------------------------------
-- The Agda standard library
--
-- Normal forms in commutative monoids
--
-- Adapted from Algebra.Solver.Monoid.Normal
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)

module Algebra.Solver.CommutativeMonoid.Normal
  {c ℓ} (M : CommutativeMonoid c ℓ) where

open import Algebra.Bundles.Raw using (RawMonoid)
import Algebra.Properties.CommutativeSemigroup as CSProperties
import Algebra.Properties.Monoid.Mult as MultProperties
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
open import Data.Vec.Relation.Binary.Equality.DecPropositional using (_≡?_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open CommutativeMonoid M
open MultProperties monoid using (_×_; ×-homo-1; ×-homo-+)
open CSProperties commutativeSemigroup using (interchange)
open ≈-Reasoning setoid

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Monoid expressions

open import Algebra.Solver.Monoid.Expression monoid public

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a vector of multiplicities (a bag).

private
  N : ℕ → Set
  N n = Vec ℕ n

-- Constructions on normal forms

-- The empty bag.

  empty : N n
  empty = replicate _ 0

-- A singleton bag.

  sg : (i : Fin n) → N n
  sg zero    = 1 ∷ empty
  sg (suc i) = 0 ∷ sg i

-- The composition of normal forms.
  infixr 10 _•_

  _•_  : (v w : N n) → N n
  _•_ = zipWith _+_

-- Packaging up the normal forms

NF : ℕ → RawMonoid _ _
NF n = record { Carrier = N n ; _≈_ = _≡_ ; _∙_ = _•_ ; ε = empty }

-- The semantics of a normal form.

⟦_⟧⇓ : N n → Env n → Carrier
⟦ []    ⟧⇓ _       = ε
⟦ n ∷ v ⟧⇓ (a ∷ ρ) = (n × a) ∙ (⟦ v ⟧⇓ ρ)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (N n)
_≟_ = _≡?_ ℕ._≟_

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty bag stands for the unit ε.

ε-homo : (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
ε-homo [] = refl
ε-homo (a ∷ ρ) = begin
    ε ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ identityˡ _ ⟩
    ⟦ empty ⟧⇓ ρ       ≈⟨ ε-homo ρ ⟩
    ε                  ∎

-- The singleton bag stands for a single variable.

sg-correct : (x : Fin n) (ρ : Env n) →  ⟦ sg x ⟧⇓ ρ ≈ lookup ρ x
sg-correct zero (x ∷ ρ) = begin
    (1 × x) ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ ∙-congʳ (×-homo-1 _) ⟩
    x ∙ ⟦ empty ⟧⇓ ρ         ≈⟨ ∙-congˡ (ε-homo ρ) ⟩
    x ∙ ε                    ≈⟨ identityʳ _ ⟩
    x                        ∎
sg-correct (suc x) (_ ∷ ρ) = begin
    ε ∙ ⟦ sg x ⟧⇓ ρ   ≈⟨ identityˡ _ ⟩
    ⟦ sg x ⟧⇓ ρ       ≈⟨ sg-correct x ρ ⟩
    lookup ρ x        ∎

-- Normal form composition corresponds to the composition of the monoid.

∙-homo : ∀ v w (ρ : Env n) →
         ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
∙-homo [] [] _ =  sym (identityˡ _)
∙-homo (l ∷ v) (m ∷ w) (a ∷ ρ) = begin
  ((l + m) × a) ∙ ⟦ v • w ⟧⇓ ρ              ≈⟨ ∙-congʳ  (×-homo-+ a l m) ⟩
  (l × a) ∙ (m × a) ∙ ⟦ v • w ⟧⇓ ρ          ≈⟨ ∙-congˡ  (∙-homo v w ρ) ⟩
  (l × a) ∙ (m × a) ∙ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ) ≈⟨ interchange _ _ _ _ ⟩
  ⟦ l ∷ v ⟧⇓ (a ∷ ρ) ∙ ⟦ m ∷ w ⟧⇓ (a ∷ ρ)   ∎

------------------------------------------------------------------------
-- Packaging everything up

normal : NormalAPI
normal = record
  { NF       = NF
  ; var      = sg
  ; _≟_      = _≟_
  ; ⟦_⟧⇓     = ⟦_⟧⇓
  ; ⟦var_⟧⇓  = sg-correct
  ; ⟦⟧⇓-homo = λ ρ → record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = λ where ≡.refl → refl }
      ; homo = λ v w → ∙-homo v w ρ
      }
    ; ε-homo = ε-homo ρ
    }
  }

open NormalAPI normal public
  using (normalise; correct)

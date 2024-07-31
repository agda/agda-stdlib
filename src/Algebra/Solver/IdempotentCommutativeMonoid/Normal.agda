------------------------------------------------------------------------
-- The Agda standard library
--
-- Normal forms in commutative monoids
--
-- Adapted from Algebra.Solver.Monoid.Normal
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (IdempotentCommutativeMonoid)

module Algebra.Solver.IdempotentCommutativeMonoid.Normal
  {c ℓ} (M : IdempotentCommutativeMonoid c ℓ) where

open import Algebra.Bundles.Raw using (RawMonoid)
import Algebra.Properties.CommutativeSemigroup as CommutativeSemigroupProperties
open import Data.Bool as Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
open import Data.Vec.Relation.Binary.Equality.DecPropositional using (_≡?_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open IdempotentCommutativeMonoid M
open CommutativeSemigroupProperties commutativeSemigroup
  using  (interchange; x∙yz≈xy∙z; x∙yz≈y∙xz)
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
  N n = Vec Bool n

-- Constructions on normal forms

-- The empty bag.

  empty : N n
  empty = replicate _ false

-- A singleton bag.

  sg : (i : Fin n) → N n
  sg zero    = true ∷ empty
  sg (suc i) = false ∷ sg i

-- The composition of normal forms.
  infixr 10 _•_

  _•_  : (v w : N n) → N n
  _•_ = zipWith _∨_

-- Packaging up the normal forms

NF : ℕ → RawMonoid _ _
NF n = record { Carrier = N n ; _≈_ = _≡_ ; _∙_ = _•_ ; ε = empty }

-- The semantics of a normal form.

⟦_⟧⇓ : N n → Env n → Carrier
⟦ []    ⟧⇓ _       = ε
⟦ b ∷ v ⟧⇓ (a ∷ ρ) = if b then a ∙ (⟦ v ⟧⇓ ρ) else (⟦ v ⟧⇓ ρ)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (N n)
_≟_ = _≡?_ Bool._≟_

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty bag stands for the unit ε.

ε-homo : (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
ε-homo [] = refl
ε-homo (a ∷ ρ) = ε-homo ρ

-- The singleton bag stands for a single variable.

sg-correct : (x : Fin n) (ρ : Env n) →  ⟦ sg x ⟧⇓ ρ ≈ lookup ρ x
sg-correct zero (x ∷ ρ) = begin
    x ∙ ⟦ empty ⟧⇓ ρ         ≈⟨ ∙-congˡ (ε-homo ρ) ⟩
    x ∙ ε                    ≈⟨ identityʳ _ ⟩
    x                        ∎
sg-correct (suc x) (_ ∷ ρ) = sg-correct x ρ

-- Normal form composition corresponds to the composition of the monoid.

distr : ∀ a b c → a ∙ (b ∙ c) ≈ (a ∙ b) ∙ (a ∙ c)
distr a b c = begin
    a ∙ (b ∙ c)        ≈⟨ ∙-congʳ (idem a) ⟨
    (a ∙ a) ∙ (b ∙ c)  ≈⟨ interchange _ _ _ _ ⟩
    (a ∙ b) ∙ (a ∙ c)  ∎

∙-homo : ∀ v w (ρ : Env n) →
         ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
∙-homo [] [] ρ = sym (identityˡ _)
∙-homo (true ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (∙-homo v w ρ)) (distr _ _ _)
∙-homo (true ∷ v) (false ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (∙-homo v w ρ)) (x∙yz≈xy∙z _ _ _)
∙-homo (false ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (∙-homo v w ρ)) (x∙yz≈y∙xz _ _ _)
∙-homo (false ∷ v) (false ∷ w) (a ∷ ρ) =
  ∙-homo v w ρ

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


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

flip12 = x∙yz≈y∙xz
{-# WARNING_ON_USAGE flip12
"Warning: flip12 was deprecated in v2.2.
Please use Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz instead."
#-}

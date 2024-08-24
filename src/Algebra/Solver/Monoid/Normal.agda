------------------------------------------------------------------------
-- The Agda standard library
--
-- Normal forms in commutative monoids
--
-- Adapted from Algebra.Solver.Monoid.Normal
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Solver.Monoid.Normal {c ℓ} (M : Monoid c ℓ) where

open import Algebra.Bundles.Raw using (RawMonoid)
import Algebra.Properties.Semigroup as SemigroupProperties
open import Data.Fin as Fin using (Fin)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; ++-[]-rawMonoid)
open import Data.List.Relation.Binary.Equality.DecPropositional using (_≡?_)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open Monoid M
open SemigroupProperties semigroup using (x∙yz≈xy∙z)
open ≈-Reasoning setoid

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Monoid expressions

open import Algebra.Solver.Monoid.Expression M public

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a list of variables.

NF : ℕ → RawMonoid _ _
NF n = ++-[]-rawMonoid (Fin n)

private

  module NF {n} = RawMonoid (NF n)

  N : ℕ → Set _
  N n = NF.Carrier {n}

-- The semantics of a normal form.

⟦_⟧⇓ : N n → Env n → Carrier
⟦ []     ⟧⇓ ρ = ε
⟦ x ∷ nf ⟧⇓ ρ = lookup ρ x ∙ ⟦ nf ⟧⇓ ρ

-- The normaliser is homomorphic with respect to _++_ =def NF._∙_.

∙-homo : (nf₁ nf₂ : N n) (ρ : Env n) →
         ⟦ nf₁ NF.∙ nf₂ ⟧⇓ ρ ≈ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ
∙-homo [] nf₂ ρ = begin
  ⟦ nf₂ ⟧⇓ ρ      ≈⟨ identityˡ _ ⟨
  ε ∙ ⟦ nf₂ ⟧⇓ ρ  ∎
∙-homo (x ∷ nf₁) nf₂ ρ = begin
  lookup ρ x ∙ ⟦ nf₁ NF.∙ nf₂ ⟧⇓ ρ        ≈⟨ ∙-congˡ (∙-homo nf₁ nf₂ ρ) ⟩
  lookup ρ x ∙ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)  ≈⟨ x∙yz≈xy∙z _ _ _ ⟩
  lookup ρ x ∙ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ    ∎

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (N n)
_≟_ = _≡?_ Fin._≟_

------------------------------------------------------------------------
-- Packaging everything up

normal : NormalAPI
normal = record
  { NF       = NF
  ; var      = [_]
  ; _≟_      = _≟_
  ; ⟦_⟧⇓     = ⟦_⟧⇓
  ; ⟦var_⟧⇓  = λ x ρ → identityʳ (lookup ρ x)
  ; ⟦⟧⇓-homo = λ ρ → record
     { isMagmaHomomorphism = record
       { isRelHomomorphism = record
         { cong = λ where ≡.refl → refl
         }
       ; homo = λ nf₁ nf₂ → ∙-homo nf₁ nf₂ ρ
       }
     ; ε-homo = refl
     }
  }

open NormalAPI normal public
  using (normalise; correct)

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
import Algebra.Properties.Monoid.Mult as MultProperties
import Algebra.Properties.Semigroup as Properties
open import Data.Fin.Base using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.DecPropositional as ≋
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable as Dec

open Monoid M
open MultProperties M using (_×_; ×-homo-1; ×-homo-+)
open Properties semigroup using (x∙yz≈xy∙z)
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
NF n = List.++-[]-rawMonoid (Fin n)

private

  N : ℕ → Set _
  N n = RawMonoid.Carrier (NF n)

-- The semantics of a normal form.

⟦_⟧⇓ : ∀ {n} → N n → Env n → Carrier
⟦ []     ⟧⇓ ρ = ε
⟦ x ∷ nf ⟧⇓ ρ = lookup ρ x ∙ ⟦ nf ⟧⇓ ρ

-- The normaliser is homomorphic with respect to _++_/_∙_.

∙-homo : ∀ {n} (nf₁ nf₂ : N n) (ρ : Env n) →
              ⟦ nf₁ ++ nf₂ ⟧⇓ ρ ≈ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)
∙-homo [] nf₂ ρ = begin
  ⟦ nf₂ ⟧⇓ ρ      ≈⟨ identityˡ _ ⟨
  ε ∙ ⟦ nf₂ ⟧⇓ ρ  ∎
∙-homo (x ∷ nf₁) nf₂ ρ = begin
  lookup ρ x ∙ ⟦ nf₁ ++ nf₂ ⟧⇓ ρ          ≈⟨ ∙-congˡ (∙-homo nf₁ nf₂ ρ) ⟩
  lookup ρ x ∙ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)  ≈⟨ x∙yz≈xy∙z _ _ _ ⟩
  lookup ρ x ∙ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ    ∎

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : ∀ {n} → DecidableEquality (N n)
nf₁ ≟ nf₂ = Dec.map′ ≋⇒≡ ≡⇒≋ (nf₁ ≋? nf₂)
  where open ≋ Fin._≟_ using (≋⇒≡; ≡⇒≋; _≋?_)

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
  using (correct)

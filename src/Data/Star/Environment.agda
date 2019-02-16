------------------------------------------------------------------------
-- The Agda standard library
--
-- Environments (heterogeneous collections)
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Star.Environment {ℓ} (Ty : Set ℓ) where

open import Level
open import Data.Star.List
open import Data.Star.Decoration
open import Data.Star.Pointer as Pointer hiding (lookup)
open import Data.Unit
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

-- Contexts, listing the types of all the elements in an environment.

Ctxt : Set ℓ
Ctxt = List Ty

-- Variables (de Bruijn indices); pointers into environments.

infix 4 _∋_

_∋_ : Ctxt → Ty → Set ℓ
Γ ∋ σ = Any (const (Lift ℓ ⊤)) (σ ≡_) Γ

vz : ∀ {Γ σ} → Γ ▻ σ ∋ σ
vz = this refl

vs : ∀ {Γ σ τ} → Γ ∋ τ → Γ ▻ σ ∋ τ
vs = that _

-- Environments. The T function maps types to element types.

Env : ∀ {e} → (Ty → Set e) → (Ctxt → Set (ℓ ⊔ e))
Env T Γ = All T Γ

-- A safe lookup function for environments.

lookup : ∀ {Γ σ} {T : Ty → Set} → Γ ∋ σ → Env T Γ → T σ
lookup i ρ with Pointer.lookup i ρ
... | result refl x = x

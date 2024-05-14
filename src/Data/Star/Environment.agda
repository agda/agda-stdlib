------------------------------------------------------------------------
-- The Agda standard library
--
-- Environments (heterogeneous collections)
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Star.Environment {ℓ} (Ty : Set ℓ) where

open import Level using (_⊔_)
open import Data.Star.List using (List)
open import Data.Star.Decoration using (All)
open import Data.Star.Pointer as Pointer using (Any; this; that; result)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Function.Base using (const; case_of_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (_▻_)

-- Contexts, listing the types of all the elements in an environment.

Ctxt : Set ℓ
Ctxt = List Ty

-- Variables (de Bruijn indices); pointers into environments.

infix 4 _∋_

_∋_ : Ctxt → Ty → Set ℓ
Γ ∋ σ = Any (const (⊤ {ℓ})) (σ ≡_) Γ

vz : ∀ {Γ σ} → Γ ▻ σ ∋ σ
vz = this refl

vs : ∀ {Γ σ τ} → Γ ∋ τ → Γ ▻ σ ∋ τ
vs = that _

-- Environments. The T function maps types to element types.

Env : ∀ {e} → (Ty → Set e) → (Ctxt → Set (ℓ ⊔ e))
Env T Γ = All T Γ

-- A safe lookup function for environments.

lookup : ∀ {Γ σ} {T : Ty → Set} → Env T Γ → Γ ∋ σ → T σ
lookup ρ i with result refl x ← Pointer.lookup ρ i = x

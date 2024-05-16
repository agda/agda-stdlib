------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Function.Endomorphism.Setoid {c e} (S : Setoid c e) where

open import Agda.Builtin.Equality

open import Algebra using (Semigroup; Magma; RawMagma; Monoid; RawMonoid)
open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid)
open import Algebra.Morphism
  using (module Definitions; IsMagmaHomomorphism; IsMonoidHomomorphism)
open Definitions using (Homomorphic₂)
open import Data.Nat.Base using (ℕ; _+_; +-rawMagma; +-0-rawMonoid)
open ℕ
open import Data.Nat.Properties using (+-semigroup; +-identityʳ)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to identity)
open import Function.Construct.Composition using () renaming (function to _∘_)
open import Function.Relation.Binary.Setoid.Equality as Eq using (_⇨_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (_Preserves_⟶_)

private
  module E = Setoid (S ⇨ S)
  open E hiding (refl)
  open Func using (cong)
------------------------------------------------------------------------
-- Basic type and functions

Endo : Set _
Endo = S ⟶ₛ S

infixr 8 _^_

private
  id : Endo
  id = identity S

_^_ : Endo → ℕ → Endo
f ^ zero  = id
f ^ suc n = f ∘ (f ^ n)

^-cong₂ : ∀ f → (f ^_) Preserves _≡_ ⟶ _≈_
^-cong₂ f {n} refl = cong (f ^ n) (Setoid.refl S)

^-homo : ∀ f → Homomorphic₂ ℕ Endo _≈_ (f ^_) _+_ _∘_
^-homo f zero    n           = Setoid.refl S
^-homo f (suc m) zero    = ^-cong₂ f (+-identityʳ m)
^-homo f (suc m) (suc n) = ^-homo f m (suc n)

------------------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≈_ _∘_
∘-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = λ {_} {_} {_} {v} x≈y u≈v → S.trans u≈v (cong v x≈y)
  }
  where
    module S = Setoid S

∘-magma : Magma (c ⊔ e) (c ⊔ e)
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≈_ _∘_
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ h g f {s} → Setoid.refl S
  }

∘-semigroup : Semigroup (c ⊔ e) (c ⊔ e)
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≈_ _∘_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = (λ f → Setoid.refl S) , (λ _ → Setoid.refl S)
  }

∘-id-monoid : Monoid (c ⊔ e) (c ⊔ e)
∘-id-monoid = record { isMonoid = ∘-id-isMonoid }

private
  ∘-rawMagma : RawMagma (c ⊔ e) (c ⊔ e)
  ∘-rawMagma = Semigroup.rawMagma ∘-semigroup

  ∘-id-rawMonoid : RawMonoid (c ⊔ e) (c ⊔ e)
  ∘-id-rawMonoid = Monoid.rawMonoid ∘-id-monoid

------------------------------------------------------------------------
-- Homomorphism

^-isSemigroupHomomorphism : ∀ f → IsMagmaHomomorphism +-rawMagma ∘-rawMagma (f ^_)
^-isSemigroupHomomorphism f = record
  { isRelHomomorphism = record { cong = ^-cong₂ f }
  ; homo = ^-homo f
  }

^-isMonoidHomoorphism : ∀ f → IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
^-isMonoidHomoorphism f = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = ^-cong₂ f }
    ; homo = ^-homo f
    }
  ; ε-homo = Setoid.refl S
  }


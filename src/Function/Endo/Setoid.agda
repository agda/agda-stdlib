------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Function.Endo.Setoid {c e} (S : Setoid c e) where

open import Agda.Builtin.Equality

open import Algebra using (Semigroup; Magma; RawMagma; Monoid; RawMonoid)
open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid)
open import Algebra.Morphism
  using (module Definitions; IsMagmaHomomorphism; IsMonoidHomomorphism)
open Definitions using (Homomorphic₂)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; +-rawMagma; +-0-rawMonoid)
open import Data.Nat.Properties using (+-semigroup; +-identityʳ)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to identity)
open import Function.Construct.Composition using () renaming (function to _∘_)
open import Function.Relation.Binary.Setoid.Equality as Eq using (_⇨_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (_Preserves_⟶_)

private
  open module E = Setoid (S ⇨ S) hiding (refl)
  module S = Setoid S
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
^-cong₂ f {n} refl = cong (f ^ n) S.refl

^-homo : ∀ f → Homomorphic₂ ℕ Endo _≈_ (f ^_) _+_ _∘_
^-homo f zero    n       = S.refl
^-homo f (suc m) zero    = ^-cong₂ f (+-identityʳ m)
^-homo f (suc m) (suc n) = ^-homo f m (suc n)

------------------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≈_ _∘_
∘-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = λ {_} {_} {_} {v} x≈y u≈v → S.trans u≈v (cong v x≈y)
  }

∘-magma : Magma (c ⊔ e) (c ⊔ e)
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≈_ _∘_
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ _ _ _ → S.refl
  }

∘-semigroup : Semigroup (c ⊔ e) (c ⊔ e)
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≈_ _∘_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = (λ _ → S.refl) , (λ _ → S.refl)
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

^-isMagmaHomomorphism : ∀ f → IsMagmaHomomorphism +-rawMagma ∘-rawMagma (f ^_)
^-isMagmaHomomorphism f = record
  { isRelHomomorphism = record { cong = ^-cong₂ f }
  ; homo = ^-homo f
  }

^-isMonoidHomomorphism : ∀ f → IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
^-isMonoidHomomorphism f = record
  { isMagmaHomomorphism = ^-isMagmaHomomorphism f
  ; ε-homo = S.refl
  }

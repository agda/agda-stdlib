------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)

module Function.Endomorphism.Setoid {c e} (S : Setoid c e) where

{-# WARNING_ON_IMPORT
"Function.Endomorphism.Setoid was deprecated in v2.1.
Use Function.Endo.Setoid instead."
#-}

open import Agda.Builtin.Equality

open import Algebra
open import Algebra.Structures
open import Algebra.Morphism; open Definitions
open import Function.Equality using (setoid; _⟶_; id; _∘_; cong)
open import Data.Nat.Base using (ℕ; _+_); open ℕ
open import Data.Nat.Properties
open import Data.Product.Base using (_,_)

import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial

private
  module E = Setoid (setoid S (Trivial.indexedSetoid S))
  open E hiding (refl)

------------------------------------------------------------------------
-- Basic type and functions

Endo : Set _
Endo = S ⟶ S

infixr 8 _^_

_^_ : Endo → ℕ → Endo
f ^ zero  = id
f ^ suc n = f ∘ (f ^ n)

^-cong₂ : ∀ f → (f ^_) Preserves _≡_ ⟶ _≈_
^-cong₂ f {n} refl = cong (f ^ n)

^-homo : ∀ f → Homomorphic₂ ℕ Endo _≈_ (f ^_) _+_ _∘_
^-homo f zero    n x≈y = cong (f ^ n) x≈y
^-homo f (suc m) n x≈y = cong f (^-homo f m n x≈y)

------------------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≈_ _∘_
∘-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = λ g f x → g (f x)
  }

∘-magma : Magma _ _
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≈_ _∘_
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ h g f x≈y → cong h (cong g (cong f x≈y))
  }

∘-semigroup : Semigroup _ _
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≈_ _∘_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = cong , cong
  }

∘-id-monoid : Monoid _ _
∘-id-monoid = record { isMonoid = ∘-id-isMonoid }

------------------------------------------------------------------------
-- Homomorphism

^-isSemigroupMorphism : ∀ f → IsSemigroupMorphism +-semigroup ∘-semigroup (f ^_)
^-isSemigroupMorphism f = record
  { ⟦⟧-cong = ^-cong₂ f
  ; ∙-homo  = ^-homo f
  }

^-isMonoidMorphism : ∀ f → IsMonoidMorphism +-0-monoid ∘-id-monoid (f ^_)
^-isMonoidMorphism f = record
  { sm-homo = ^-isSemigroupMorphism f
  ; ε-homo  = λ x≈y → x≈y
  }

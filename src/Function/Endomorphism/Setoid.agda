------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Endomorphism.Setoid {c e} (S : Setoid c e) where

open import Agda.Builtin.Equality

open import Algebra
open import Algebra.Structures
open import Algebra.Morphism; open Definitions
open import Function.Equality
open import Data.Nat.Base using (ℕ; _+_); open ℕ
open import Data.Nat.Properties
open import Data.Product

import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial

private
  module E = Setoid (setoid S (Trivial.indexedSetoid S))
  open E hiding (refl)

------------------------------------------------------------------------
-- Basic type and functions

Endo : Set _
Endo = S ⟶ S

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

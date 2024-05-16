------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
module Function.Endo.Propositional {a} (A : Set a) where

open import Algebra using (Semigroup; Magma; RawMagma; Monoid; RawMonoid)
open import Algebra.Core
open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid)
open import Algebra.Morphism
  using (module Definitions; IsMagmaHomomorphism; IsMonoidHomomorphism)
open Definitions using (Homomorphic₂)

open import Data.Nat.Base using (ℕ; zero; suc; _+_; +-rawMagma; +-0-rawMonoid)
open import Data.Nat.Properties using (+-0-monoid; +-semigroup)
open import Data.Product.Base using (_,_)

open import Function.Base using (id; _∘′_; _∋_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡

import Function.Endo.Setoid (≡.setoid A) as Setoid

Endo : Set a
Endo = A → A

------------------------------------------------------------------------
-- Conversion back and forth with the Setoid-based notion of Endomorphism

fromSetoidEndo : Setoid.Endo → Endo
fromSetoidEndo = _⟨$⟩_

toSetoidEndo : Endo → Setoid.Endo
toSetoidEndo f = record
  { to = f
  ; cong  = cong f
  }

------------------------------------------------------------------------
-- N-th composition

infixr 8 _^_

_^_ : Endo → ℕ → Endo
f ^ zero  = id
f ^ suc n = f ∘′ (f ^ n)

^-homo : ∀ f → Homomorphic₂ ℕ Endo _≡_ (f ^_) _+_ _∘′_
^-homo f zero    n = refl
^-homo f (suc m) n = cong (f ∘′_) (^-homo f m n)

------------------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≡_ (Op₂ Endo ∋ _∘′_)
∘-isMagma = record
  { isEquivalence = ≡.isEquivalence
  ; ∙-cong        = cong₂ _∘′_
  }

∘-magma : Magma _ _
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≡_ (Op₂ Endo ∋ _∘′_)
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ _ _ _ → refl
  }

∘-semigroup : Semigroup _ _
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≡_ _∘′_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = (λ _ → refl) , (λ _ → refl)
  }

∘-id-monoid : Monoid _ _
∘-id-monoid = record { isMonoid = ∘-id-isMonoid }

private
  ∘-rawMagma : RawMagma a a
  ∘-rawMagma = Semigroup.rawMagma ∘-semigroup

  ∘-id-rawMonoid : RawMonoid a a
  ∘-id-rawMonoid = Monoid.rawMonoid ∘-id-monoid

------------------------------------------------------------------------
-- Homomorphism

^-isMagmaHomomorphism : ∀ f → IsMagmaHomomorphism +-rawMagma ∘-rawMagma (f ^_)
^-isMagmaHomomorphism f = record
  { isRelHomomorphism = record { cong = cong (f ^_) }
  ; homo = ^-homo f
  }

^-isMonoidHomomorphism : ∀ f → IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
^-isMonoidHomomorphism f = record
  { isMagmaHomomorphism = ^-isMagmaHomomorphism f
  ; ε-homo = refl
  }

------------------------------------------------------------------------
-- Deprecations

-- Version 2.1

^-isSemigroupMorphism = ^-isMagmaHomomorphism
{-# WARNING_ON_USAGE ^-isSemigroupMorphism
"Warning: ^-isSemigroupMorphism was deprecated in v2.1.
Please use ^-isMagmaHomomorphism instead."
#-}

^-isMonoidMorphism = ^-isMonoidHomomorphism
{-# WARNING_ON_USAGE ^-isMonoidMorphism
"Warning: ^-isMonoidMorphism was deprecated in v2.1.
Please use ^-isMonoidHomomorphism instead."
#-}

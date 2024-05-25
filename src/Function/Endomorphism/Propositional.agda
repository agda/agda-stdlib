------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Endomorphism.Propositional {a} (A : Set a) where

{-# WARNING_ON_IMPORT
"Function.Endomorphism.Propositional was deprecated in v2.1.
Use Function.Endo.Propositional instead."
#-}

open import Algebra
open import Algebra.Morphism; open Definitions

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-0-monoid; +-semigroup)
open import Data.Product.Base using (_,_)

open import Function.Base using (id; _∘′_; _∋_)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡

import Function.Endomorphism.Setoid (≡.setoid A) as Setoid

Endo : Set a
Endo = A → A

------------------------------------------------------------------------
-- Conversion back and forth with the Setoid-based notion of Endomorphism

fromSetoidEndo : Setoid.Endo → Endo
fromSetoidEndo = _⟨$⟩_

toSetoidEndo : Endo → Setoid.Endo
toSetoidEndo f = record
  { _⟨$⟩_ = f
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

------------------------------------------------------------------------
-- Homomorphism

^-isSemigroupMorphism : ∀ f → IsSemigroupMorphism +-semigroup ∘-semigroup (f ^_)
^-isSemigroupMorphism f = record
  { ⟦⟧-cong = cong (f ^_)
  ; ∙-homo  = ^-homo f
  }

^-isMonoidMorphism : ∀ f → IsMonoidMorphism +-0-monoid ∘-id-monoid (f ^_)
^-isMonoidMorphism f = record
  { sm-homo = ^-isSemigroupMorphism f
  ; ε-homo  = refl
  }

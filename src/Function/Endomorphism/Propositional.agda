------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
module Function.Endomorphism.Propositional {a} (A : Set a) where

open import Algebra
open import Algebra.Structures
open import Algebra.Morphism
open Definitions

open import Data.Nat.Base using (ℕ; _+_; zero; suc; +-rawMagma; +-0-rawMonoid)
open import Data.Nat.Properties using (+-0-monoid; +-semigroup)
open import Data.Product.Base using (_,_)

open import Function.Base using (id; _∘′_; _∋_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
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

^-isSemigroupMorphism : ∀ f → IsSemigroupHomomorphism +-rawMagma ∘-rawMagma (f ^_)
^-isSemigroupMorphism f = record
  { isRelHomomorphism = record { cong = cong (f ^_) }
  ; homo = ^-homo f
  }

^-isMonoidMorphism : ∀ f → IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
^-isMonoidMorphism f = record
  { isMagmaHomomorphism = ^-isSemigroupMorphism f
  ; ε-homo = refl
  }

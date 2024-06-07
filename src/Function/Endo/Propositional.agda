------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Endo.Propositional {a} (A : Set a) where

open import Algebra using (Semigroup; Magma; RawMagma; Monoid; RawMonoid)
open import Algebra.Core
import Algebra.Definitions.RawMonoid as RawMonoidDefinitions
import Algebra.Properties.Monoid.Mult as MonoidMultProperties
open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid)
open import Algebra.Morphism
  using (module Definitions; IsMagmaHomomorphism; IsMonoidHomomorphism)
open Definitions using (Homomorphic₂)

open import Data.Nat.Base using (ℕ; zero; suc; _+_; +-rawMagma; +-0-rawMonoid)
open import Data.Nat.Properties using (+-0-monoid; +-semigroup)
open import Data.Product.Base using (_,_)

open import Function.Base using (id; _∘′_; _∋_; flip)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡

import Function.Endo.Setoid (≡.setoid A) as Setoid

------------------------------------------------------------------------
-- Basic type and raw bundles

Endo : Set a
Endo = A → A

private

  _∘_ : Op₂ Endo
  _∘_ = _∘′_

  ∘-id-rawMonoid : RawMonoid a a
  ∘-id-rawMonoid = record { Carrier = Endo; _≈_ = _≡_ ; _∙_ = _∘_ ; ε = id }

  open RawMonoid ∘-id-rawMonoid
    using ()
    renaming (rawMagma to ∘-rawMagma)


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
-- Structures

∘-isMagma : IsMagma _≡_ _∘_
∘-isMagma = record
  { isEquivalence = ≡.isEquivalence
  ; ∙-cong        = cong₂ _∘_
  }

∘-magma : Magma _ _
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≡_ _∘_
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ _ _ _ → refl
  }

∘-semigroup : Semigroup _ _
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≡_ _∘_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = (λ _ → refl) , (λ _ → refl)
  }

∘-id-monoid : Monoid _ _
∘-id-monoid = record { isMonoid = ∘-id-isMonoid }

------------------------------------------------------------------------
-- n-th iterated composition

infixr 8 _^_

_^_ : Endo → ℕ → Endo
_^_ = flip _×_ where open RawMonoidDefinitions ∘-id-rawMonoid using (_×_)

------------------------------------------------------------------------
-- Homomorphism

module _ (f : Endo) where

  open MonoidMultProperties ∘-id-monoid using (×-homo-+)

  ^-homo : Homomorphic₂ ℕ Endo _≡_ (f ^_) _+_ _∘_
  ^-homo = ×-homo-+ f

  ^-isMagmaHomomorphism : IsMagmaHomomorphism +-rawMagma ∘-rawMagma (f ^_)
  ^-isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = cong (f ^_) }
    ; homo = ^-homo
    }

  ^-isMonoidHomomorphism : IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
  ^-isMonoidHomomorphism = record
    { isMagmaHomomorphism = ^-isMagmaHomomorphism
    ; ε-homo = refl
    }

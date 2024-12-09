------------------------------------------------------------------------
-- The Agda standard library
--
-- Endomorphisms on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Function.Endo.Setoid {c e} (S : Setoid c e) where

open import Agda.Builtin.Equality using (_≡_)

open import Algebra using (Semigroup; Magma; RawMagma; Monoid; RawMonoid)
import Algebra.Definitions.RawMonoid as RawMonoidDefinitions
import Algebra.Properties.Monoid.Mult as MonoidMultProperties
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
-- Basic type and raw bundles

Endo : Set _
Endo = S ⟶ₛ S

private
  id : Endo
  id = identity S

  ∘-id-rawMonoid : RawMonoid (c ⊔ e) (c ⊔ e)
  ∘-id-rawMonoid = record { Carrier = Endo; _≈_ = _≈_ ; _∙_ = _∘_ ; ε = id }

  open RawMonoid ∘-id-rawMonoid
    using ()
    renaming (rawMagma to ∘-rawMagma)

--------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≈_ _∘_
∘-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = λ {_} {_} {_} {k} f≈g h≈k x → S.trans (h≈k _) (cong k (f≈g x))
  }

∘-magma : Magma (c ⊔ e) (c ⊔ e)
∘-magma = record { isMagma = ∘-isMagma }

∘-isSemigroup : IsSemigroup _≈_ _∘_
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = λ _ _ _ _ → S.refl
  }

∘-semigroup : Semigroup (c ⊔ e) (c ⊔ e)
∘-semigroup = record { isSemigroup = ∘-isSemigroup }

∘-id-isMonoid : IsMonoid _≈_ _∘_ id
∘-id-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = (λ _ _ → S.refl) , (λ _ _ → S.refl)
  }

∘-id-monoid : Monoid (c ⊔ e) (c ⊔ e)
∘-id-monoid = record { isMonoid = ∘-id-isMonoid }

------------------------------------------------------------------------
-- -- n-th iterated composition

infixr 8 _^_

_^_ : Endo → ℕ → Endo
f ^ n = n × f where open RawMonoidDefinitions ∘-id-rawMonoid using (_×_)

------------------------------------------------------------------------
-- Homomorphism

module _ (f : Endo) where

  open MonoidMultProperties ∘-id-monoid using (×-congˡ; ×-homo-+)

  ^-cong₂ : (f ^_) Preserves _≡_ ⟶ _≈_
  ^-cong₂ = ×-congˡ {f}

  ^-homo : Homomorphic₂ ℕ Endo _≈_ (f ^_) _+_ _∘_
  ^-homo = ×-homo-+ f

  ^-isMagmaHomomorphism : IsMagmaHomomorphism +-rawMagma ∘-rawMagma (f ^_)
  ^-isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = ^-cong₂ }
    ; homo = ^-homo
    }

  ^-isMonoidHomomorphism : IsMonoidHomomorphism +-0-rawMonoid ∘-id-rawMonoid (f ^_)
  ^-isMonoidHomomorphism = record
    { isMagmaHomomorphism = ^-isMagmaHomomorphism
    ; ε-homo = λ _ → S.refl
    }


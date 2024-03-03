------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality over indexed container extensions parametrised by a setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Setoid)

module Data.Container.Indexed.Relation.Binary.Equality.Setoid
  {ℓⁱ ℓᶜ ℓᵉ} {I : Set ℓⁱ} (S : I → Setoid ℓᶜ ℓᵉ)
  where

open import Function
open import Level using (Level; _⊔_; suc)
open import Relation.Binary

open import Data.Container.Indexed.Core
open import Data.Container.Indexed.Relation.Binary.Pointwise
import Data.Container.Indexed.Relation.Binary.Pointwise.Properties
  as Pointwise

open Setoid using (Carrier; _≈_)

private variable
  ℓˢ ℓᵖ : Level
  O : Set _

------------------------------------------------------------------------
-- Definition of equality

module _ (C : Container I O ℓˢ ℓᵖ) (o : O) where

  Eq : Rel (⟦ C ⟧ (Carrier ∘ S) o) (ℓᵉ ⊔ ℓˢ ⊔ ℓᵖ)
  Eq = Pointwise C (_≈_ ∘ S) o

------------------------------------------------------------------------
-- Relational properties

  refl : Reflexive Eq
  refl = Pointwise.refl C _ (Setoid.refl ∘ S)

  sym : Symmetric Eq
  sym = Pointwise.sym C _ (Setoid.sym ∘ S)

  trans : Transitive Eq
  trans = Pointwise.trans C _ (Setoid.trans ∘ S)

  isEquivalence : IsEquivalence Eq
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  setoid : Setoid (ℓˢ ⊔ ℓᵖ ⊔ ℓᶜ) (ℓˢ ⊔ ℓᵖ ⊔ ℓᵉ)
  setoid = record
    { isEquivalence = isEquivalence
    }

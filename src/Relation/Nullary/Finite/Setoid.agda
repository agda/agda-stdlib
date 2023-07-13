------------------------------------------------------------------------
-- The Agda standard library
--
-- Notions of finiteness for setoids
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Relation.Nullary.Finite.Setoid where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as ×
open import Data.Sum.Base as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function
open import Level renaming (suc to lsuc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetR
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    c ℓ c′ ℓ′ : Level

record StrictlyFinite (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
   field
     size : ℕ
     inv : Inverse X (≡.setoid (Fin size))

record Subfinite (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    inj : Injection X (≡.setoid (Fin size))

record FinitelyEnumerable (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    srj : Surjection (≡.setoid (Fin size)) X

record InjectsIntoFinitelyEnumerable (X : Setoid c ℓ) c′ ℓ′
       : Set (c ⊔ ℓ ⊔ lsuc (c′ ⊔ ℓ′)) where
  field
    Apex : Setoid c′ ℓ′
    finitelyEnumerable : FinitelyEnumerable Apex
    inj : Injection X Apex

  open FinitelyEnumerable finitelyEnumerable public

record SurjectionFromFinitelyEnumerable (X : Setoid c ℓ) c′ ℓ′
       : Set (c ⊔ ℓ ⊔ lsuc (c′ ⊔ ℓ′)) where
  field
    Apex : Setoid c′ ℓ′
    subfinite : Subfinite Apex
    srj : Surjection Apex X

  open Subfinite subfinite public

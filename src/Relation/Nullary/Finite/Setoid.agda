------------------------------------------------------------------------
-- The Agda standard library
--
-- Notions of finiteness for setoids
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Relation.Nullary.Finite.Setoid where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Function.Bundles using (Injection; Surjection; Inverse)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

private
  variable
    c ℓ c′ ℓ′ : Level

record IsStronglyFinite (X : Setoid c ℓ) (n : ℕ) : Set (c ⊔ ℓ) where
   field
     inv : Inverse X (setoid (Fin n))

record StronglyFinite (X : Setoid c ℓ) (n : ℕ) : Set (c ⊔ ℓ) where
   field
     isFinite : IsStronglyFinite X n

record Subfinite (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    inj : Injection X (setoid (Fin size))

record FinitelyEnumerable (X : Setoid c ℓ) : Set (c ⊔ ℓ) where
  field
    size : ℕ
    srj : Surjection (setoid (Fin size)) X

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

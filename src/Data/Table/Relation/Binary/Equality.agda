------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Vec.Functional` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from other Table modules
{-# OPTIONS --warn=noUserWarning #-}

module Data.Table.Relation.Binary.Equality where

{-# WARNING_ON_IMPORT
"Data.Table.Relation.Binary.Equality was deprecated in v1.2.
Use Data.Vec.Functional.Relation.Binary.Pointwise instead."
#-}

open import Relation.Binary using (Setoid)
open import Data.Table.Base
open import Data.Nat.Base using (ℕ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_)

setoid : ∀ {c p} → Setoid c p → ℕ → Setoid _ _
setoid S n = record
  { Carrier = Table Carrier n
  ; _≈_ = λ t t′ → ∀ i → lookup t i ≈ lookup t′ i
  ; isEquivalence = record
    { refl  = λ i → refl
    ; sym   = λ p → sym ∘ p
    ; trans = λ p q i → trans (p i) (q i)
    }
  }
  where open Setoid S

≡-setoid : ∀ {a} → Set a → ℕ → Setoid _ _
≡-setoid A = setoid (P.setoid A)

module _ {a} {A : Set a} {n} where
  open Setoid (≡-setoid A n) public
    using () renaming (_≈_ to _≗_)

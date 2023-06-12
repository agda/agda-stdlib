------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors with faster indexing based on binary numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Binary.Base where

open import Data.Nat.Binary.Base
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    n : ℕᵇ

-- Core type
------------------------------------------------------------------------

data Vecᵇ (A : Set a) : ℕᵇ → Set a where
  -- The empty vector
  []        :                               Vecᵇ A zero
  -- A vector with an odd number of elements
  _∷⟨_/_⟩   : A     → Vecᵇ A n → Vecᵇ A n → Vecᵇ A 1+[2 n ]
  -- A vector with a non-zero even number of elements
  _×_∷⟨_/_⟩ : A → A → Vecᵇ A n → Vecᵇ A n → Vecᵇ A 2[1+ n ]

-- Operations on the front of a vector
------------------------------------------------------------------------

-- Prepend an element to a vector.
_∷_ : A → Vecᵇ A n → Vecᵇ A (suc n)
x ∷ [] = x ∷⟨ [] / [] ⟩
x ∷ (y ∷⟨ ls / rs ⟩) = x × y ∷⟨ ls / rs ⟩
x ∷ (y × z ∷⟨ ls / rs ⟩) = x ∷⟨ y ∷ ls / z ∷ rs ⟩

-- Extract the first element of a vector.
head : Vecᵇ A (suc n) → A
head {n = zero}     (x     ∷⟨ [] / [] ⟩) = x
head {n = 2[1+ n ]} (x     ∷⟨ _  / _  ⟩) = x
head {n = 1+[2 n ]} (x × _ ∷⟨ _  / _  ⟩) = x

-- Interleave two non-empty vectors.
-- This is intended to be an auxillary function for 'tail' but it is exposed so
-- that we can prove its properties.
merge : Vecᵇ A (suc n) → Vecᵇ A (suc n) → Vecᵇ A 2[1+ n ]
merge {n = zero} (x₁ ∷⟨ [] / [] ⟩) (x₂ ∷⟨ [] / [] ⟩) = x₁ × x₂ ∷⟨ [] / [] ⟩
merge {n = 2[1+ n ]} (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = x₁ × x₂ ∷⟨ merge ls₁ rs₁ / merge ls₂ rs₂ ⟩
merge {n = 1+[2 n ]} (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = x₁ × x₂ ∷⟨ y₁ ∷⟨ ls₁ / rs₁ ⟩ / y₂ ∷⟨ ls₂ / rs₂ ⟩ ⟩

-- Remove the first element of a vector and return the remainder.
tail : Vecᵇ A (suc n) → Vecᵇ A n
tail {n = zero} (x ∷⟨ [] / [] ⟩) = []
tail {n = 2[1+ n ]} (x ∷⟨ ls / rs ⟩) = merge ls rs
tail {n = 1+[2 n ]} (x × y ∷⟨ ls / rs ⟩) = y ∷⟨ ls / rs ⟩

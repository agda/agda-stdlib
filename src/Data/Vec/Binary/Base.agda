------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors with faster indexing based on binary numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Binary.Base where

open import Data.Fin.Binary.Base
open import Data.Nat.Binary.Base
open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
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

-- Indexing
------------------------------------------------------------------------

lookup : Vecᵇ A n → Finᵇ n → A
lookup (x ∷⟨ ls / rs ⟩) zeroᵒ = x
lookup (x ∷⟨ ls / rs ⟩) 1+[2 i ]ᵒ = lookup ls i
lookup (x ∷⟨ ls / rs ⟩) 2[1+ i ]ᵒ = lookup rs i
lookup (x × y ∷⟨ ls / rs ⟩) zeroᵉ = x
lookup (x × y ∷⟨ ls / rs ⟩) oneᵉ = y
lookup (x × y ∷⟨ ls / rs ⟩) 2[1+ i ]ᵉ = lookup ls i
lookup (x × y ∷⟨ ls / rs ⟩) 3+[2 i ]ᵉ = lookup rs i


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

-- Shape-preserving operations
------------------------------------------------------------------------

-- Construct a vector from one element
replicate : A → Vecᵇ A n
replicate {n = zero} x = []
replicate {n = 2[1+ n ]} x = x × x ∷⟨ replicate x / replicate x ⟩
replicate {n = 1+[2 n ]} x = x ∷⟨ replicate x / replicate x ⟩

-- Apply a function to each element of a vector
map : (A → B) → Vecᵇ A n → Vecᵇ B n
map f [] = []
map f (x ∷⟨ ls / rs ⟩) = f x ∷⟨ map f ls / map f rs ⟩
map f (x × y ∷⟨ ls / rs ⟩) = f x × f y ∷⟨ map f ls / map f rs ⟩

-- Apply a binary operation to the corresponding elements of two vectors
zipWith : (A → B → C) → Vecᵇ A n → Vecᵇ B n → Vecᵇ C n
zipWith f [] [] = []
zipWith f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = f x₁ x₂ ∷⟨ zipWith f ls₁ ls₂ / zipWith f rs₁ rs₂ ⟩
zipWith f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = f x₁ x₂ × f y₁ y₂ ∷⟨ zipWith f ls₁ ls₂ / zipWith f rs₁ rs₂ ⟩

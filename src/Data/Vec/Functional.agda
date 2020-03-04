------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined as functions from a finite set to a type.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional where

open import Data.Vec.Functional.Base public

open import Data.Bool.Base using (true; false)
open import Data.Fin using (Fin; _≟_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (Inverse; _↔_)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (⌊_⌋)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- Changes the order of elements in the table according to a permutation (i.e.
-- an 'Inverse' object on the indices).

permute : ∀ {m n a} {A : Set a} → Fin m ↔ Fin n → Vector A n → Vector A m
permute π = rearrange (Inverse.to π ⟨$⟩_)

-- The result of 'select z i t' takes the value of 'lookup t i' at index 'i',
-- and 'z' everywhere else.

select : ∀ {n} {a} {A : Set a} → A → Fin n → Vector A n → Vector A n
select z i t j with does (j ≟ i)
... | true  = t i
... | false = z

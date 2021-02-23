------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Vec.Functional` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from other Table modules
{-# OPTIONS --warn=noUserWarning #-}

module Data.Table where

{-# WARNING_ON_IMPORT
"Data.Table was deprecated in v1.2.
Use Data.Vec.Functional instead."
#-}

open import Data.Table.Base public

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

permute : ∀ {m n a} {A : Set a} → Fin m ↔ Fin n → Table A n → Table A m
permute π = rearrange (Inverse.to π ⟨$⟩_)

-- The result of 'select z i t' takes the value of 'lookup t i' at index 'i',
-- and 'z' everywhere else.

select : ∀ {n} {a} {A : Set a} → A → Fin n → Table A n → Table A n
lookup (select z i t) j with does (j ≟ i)
... | true  = lookup t i
... | false = z

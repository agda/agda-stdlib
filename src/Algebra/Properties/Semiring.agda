------------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items for arbitrary Semiring
------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Semiring {α α≈} (R : Semiring α α≈) where

open import Data.Product using (Σ)
open import Relation.Binary using (Setoid) renaming (Decidable to Decidable₂)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred; Decidable)
open Semiring R
open Setoid setoid using (_≉_)

------------------------------------------------------------------------------
-- The general notion of a nonzero element

IsNonzero : Pred Carrier α≈
IsNonzero = (_≉ 0#)

Nonzero : Set _
Nonzero = Σ Carrier IsNonzero

nonzero? : (_≟_ : Decidable₂ _≈_) → Decidable IsNonzero
nonzero? _≟_ x  with x ≟ 0#
... | no ne   =  yes ne
... | yes x≈0 =  no (\x≉0 → x≉0 x≈0)

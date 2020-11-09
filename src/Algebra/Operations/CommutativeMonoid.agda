------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated Table
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Fin.Base using (Fin; zero)
open import Data.Table.Base as Table using (Table)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Algebra.Operations.CommutativeMonoid
  {s₁ s₂} (CM : CommutativeMonoid s₁ s₂)
  where

{-# WARNING_ON_IMPORT
"Algebra.Operations.CommutativeMonoid was deprecated in v1.5.
Use Algebra.Properties.CommutativeMonoid.(Summation/Multiplication) instead."
#-}

open CommutativeMonoid CM
  renaming
  ( _∙_       to _+_
  ; ε         to 0#
  )

-- Summation over lists/tables

sumₗ : List Carrier → Carrier
sumₗ = List.foldr _+_ 0#

sumₜ : ∀ {n} → Table Carrier n → Carrier
sumₜ = Table.foldr _+_ 0#

-- An alternative mathematical-style syntax for sumₜ

infixl 10 sumₜ-syntax

sumₜ-syntax : ∀ n → (Fin n → Carrier) → Carrier
sumₜ-syntax _ = sumₜ ∘ Table.tabulate

syntax sumₜ-syntax n (λ i → x) = ∑[ i < n ] x

------------------------------------------------------------------------
-- Operations

open import Algebra.Properties.Monoid.Multiplication public

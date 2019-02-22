------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Binary.Equality.DecPropositional directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module Data.List.Relation.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ public

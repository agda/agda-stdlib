------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.Vec.Relation.Binary.Equality.DecPropositional directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Data.Vec.Relation.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

open import Data.Vec.Relation.Binary.Equality.DecPropositional _≟_ public

{-# WARNING_ON_IMPORT
"Data.Vec.Relation.Equality.DecPropositional was deprecated in v1.0.
Use Data.Vec.Relation.Binary.Equality.DecPropositional instead."
#-}

------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument relevance used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Relevance where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-exporting the builtins publically

open import Agda.Builtin.Reflection public using (Relevance)
open Relevance public

_≟_ : Decidable (_≡_ {A = Relevance})
relevant   ≟ relevant   = yes refl
irrelevant ≟ irrelevant = yes refl
relevant   ≟ irrelevant = no λ()
irrelevant ≟ relevant   = no λ()

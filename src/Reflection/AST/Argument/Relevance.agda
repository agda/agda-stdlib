------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument relevance used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument.Relevance where

open import Relation.Nullary                           using (yes; no)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (refl)

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Relevance)
open Relevance public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_

_≟_ : DecidableEquality Relevance
relevant   ≟ relevant   = yes refl
irrelevant ≟ irrelevant = yes refl
relevant   ≟ irrelevant = no λ()
irrelevant ≟ relevant   = no λ()

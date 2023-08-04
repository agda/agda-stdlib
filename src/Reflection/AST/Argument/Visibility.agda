------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument visibility used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument.Visibility where

open import Relation.Nullary                           using (yes; no)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (refl)

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Visibility)
open Visibility public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_

_≟_ : DecidableEquality Visibility
visible   ≟ visible   = yes refl
hidden    ≟ hidden    = yes refl
instance′ ≟ instance′ = yes refl
visible   ≟ hidden    = no λ()
visible   ≟ instance′ = no λ()
hidden    ≟ visible   = no λ()
hidden    ≟ instance′ = no λ()
instance′ ≟ visible   = no λ()
instance′ ≟ hidden    = no λ()

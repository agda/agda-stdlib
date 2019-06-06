------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument visibility used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Visibility where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-exporting the builtins publically

open import Agda.Builtin.Reflection public using (Visibility)
open Visibility public

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

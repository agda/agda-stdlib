------------------------------------------------------------------------
-- The Agda standard library
--
-- Patterns used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Pattern where

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection public using (Pattern)
open Pattern public

------------------------------------------------------------------------
-- Re-exporting definitions that used to be here

open import Reflection.AST.Term public
  using    ( proj-injective )
  renaming ( pat-con-injective₁ to con-injective₁
           ; pat-con-injective₂ to con-injective₂
           ; pat-con-injective  to con-injective
           ; pat-var-injective  to var-injective
           ; pat-lit-injective  to lit-injective
           ; _≟-Patterns_       to _≟s_
           ; _≟-Pattern_        to _≟_
           )

------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.FunctionProperties.Consequences.Propositional
  {a} {A : Set a} where

{-# WARNING_ON_IMPORT
"Algebra.FunctionProperties.Consequences.Propositional was deprecated in v1.3.
Use Algebra.Consequences.Propositional instead."
#-}

open import Algebra.Consequences.Propositional {A = A} public

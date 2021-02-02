------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated
-- Algebra.Operations.CommutativeMonoid
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra
import Algebra.Operations.CommutativeMonoid as MonoidOperations

module Algebra.Operations.Semiring {s₁ s₂} (S : Semiring s₁ s₂) where

{-# WARNING_ON_IMPORT
"Algebra.Operations.Semiring was deprecated in v1.5.
Use Algebra.Properties.Semiring.(Mult/Exp) instead."
#-}

open Semiring S

------------------------------------------------------------------------
-- Re-exports

open MonoidOperations +-commutativeMonoid public
open import Algebra.Properties.Semiring.Exponentiation S public
open import Algebra.Properties.Semiring.Multiplication S public
  using (×1-homo-*; ×′1-homo-*)

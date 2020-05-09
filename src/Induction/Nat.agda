------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the Data.(Nat/Fin).Induction
-- modules directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Induction.Nat where

open import Data.Nat.Induction public
open import Data.Fin.Induction public

{-# WARNING_ON_IMPORT
"Induction.Nat was deprecated in v1.1.
Use Data.Nat.Induction and Data.Fin.Induction instead."
#-}

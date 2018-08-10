------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

module Codata.Cofin.Literals where

open import Agda.Builtin.FromNat
open import Codata.Conat
open import Codata.Cofin

number : ∀ n → Number (Cofin n)
number n = record
  { Constraint = _ℕ< n
  ; fromNat    = λ n {{p}} → fromℕ< p
  }


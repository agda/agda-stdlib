------------------------------------------------------------------------
-- The Agda standard library
--
-- Null instance for ℕ
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Nat.Relation.Unary.Null where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Relation.Unary.Null

------------------------------------------------------------------------
-- Specimen reimplementation

open import Agda.Builtin.Nat
  using (div-helper; mod-helper)

-- Division
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_/_ : (dividend divisor : ℕ) → .{{NonZero divisor}} → ℕ
m / n@(suc n-1) = div-helper 0 n-1 m n-1

-- Remainder/modulus
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_%_ : (dividend divisor : ℕ) → .{{NonZero divisor}} → ℕ
m % n@(suc n-1) = mod-helper 0 n-1 m n-1

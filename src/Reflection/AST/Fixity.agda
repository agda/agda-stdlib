------------------------------------------------------------------------
-- The Agda standard library
--
-- AST fixity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.AST.Fixity where

import Agda.Builtin.Reflection as Builtin
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Float.Base using () renaming (_≤ᵇ_ to _≤ᶠ_)
open import Level using (zero)
open import Relation.Binary.Core using (Rel)

open Builtin public
  using (non-assoc; related; unrelated; fixity; Fixity; Precedence)
  renaming
  ( left-assoc      to assocˡ
  ; right-assoc     to assocʳ
  ; primQNameFixity to getFixity
  )

-- Partial order on Precedence
_≤ᵇ_ : Precedence → Precedence → Bool
related x ≤ᵇ related y = x ≤ᶠ y
related x ≤ᵇ unrelated = true
unrelated ≤ᵇ related x = false
unrelated ≤ᵇ unrelated = true

_≤_ : Rel Precedence zero
x ≤ y = T (x ≤ᵇ y)


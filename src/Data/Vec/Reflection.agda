------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities for Vector
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Reflection where

import Data.List.Base as List
open import Data.Vec.Base
open import Reflection.AST.Term
open import Reflection.AST.Argument

------------------------------------------------------------------------
-- Type

`Vector : Term → Term → Term
`Vector `A `n = def (quote Vec) (1 ⋯⟅∷⟆ `A ⟨∷⟩ `n ⟨∷⟩ List.[])

------------------------------------------------------------------------
-- Constructors

`[] : Term
`[] = con (quote []) (2 ⋯⟅∷⟆ List.[])

infixr 5 _`∷_

_`∷_ : Term → Term → Term
_`∷_ x xs = con (quote _∷_) (3 ⋯⟅∷⟆ x ⟨∷⟩ xs ⟨∷⟩ List.[])

------------------------------------------------------------------------
-- Patterns

-- Can't be used on the RHS as the omitted args aren't inferable.

pattern `[]`       = con (quote [])  (_ ∷ _ ∷ [])
pattern _`∷`_ x xs = con (quote _∷_) (_ ∷ _ ∷ _ ∷ x ⟨∷⟩ xs ⟨∷⟩ _)

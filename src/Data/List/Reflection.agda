------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities for List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Reflection where

open import Data.List.Base
open import Reflection.AST.Term
open import Reflection.AST.Argument

------------------------------------------------------------------------
-- Type

`List : Term → Term
`List `A = def (quote List) (1 ⋯⟅∷⟆ `A ⟨∷⟩ [])

------------------------------------------------------------------------
-- Constructors

`[] : Term
`[] = con (quote List.[]) (2 ⋯⟅∷⟆ [])

infixr 5 _`∷_

_`∷_ : Term → Term → Term
x `∷ xs = con (quote List._∷_) (2 ⋯⟅∷⟆ x ⟨∷⟩ xs ⟨∷⟩ [])

------------------------------------------------------------------------
-- Patterns

-- Can't be used on the RHS as the omitted args aren't inferable
pattern `[]`       = con (quote List.[])  _
pattern _`∷`_ x xs = con (quote List._∷_) (_ ∷ _ ∷ x ⟨∷⟩ xs ⟨∷⟩ _)

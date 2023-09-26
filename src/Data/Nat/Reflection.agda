------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities for ℕ
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Reflection where

open import Data.Nat.Base as ℕ
import Data.Fin.Base as Fin
open import Data.List.Base using ([])
open import Reflection.AST.Term
open import Reflection.AST.Argument

------------------------------------------------------------------------
-- Term

pattern `ℕ     = def (quote ℕ) []
pattern `zero  = con (quote zero) []
pattern `suc x = con (quote suc) (x ⟨∷⟩ [])

toTerm : ℕ → Term
toTerm zero    = `zero
toTerm (suc i) = `suc (toTerm i)

toFinTerm : ℕ → Term
toFinTerm zero    = con (quote Fin.zero) (1 ⋯⟅∷⟆ [])
toFinTerm (suc i) = con (quote Fin.suc)  (1 ⋯⟅∷⟆ toFinTerm i ⟨∷⟩ [])

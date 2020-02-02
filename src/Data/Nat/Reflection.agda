------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities for ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Reflection where

open import Data.Nat.Base as ℕ
open import Data.Fin.Base as Fin
open import Data.List.Base using ([])
open import Reflection.Term
open import Reflection.Argument

------------------------------------------------------------------------
-- Term

toTerm : ℕ → Term
toTerm zero    = con (quote ℕ.zero) []
toTerm (suc i) = con (quote ℕ.suc)  (toTerm i ⟨∷⟩ [])

toFinTerm : ℕ → Term
toFinTerm zero    = con (quote Fin.zero) (1 ⋯⟅∷⟆ [])
toFinTerm (suc i) = con (quote Fin.suc)  (1 ⋯⟅∷⟆ toFinTerm i ⟨∷⟩ [])

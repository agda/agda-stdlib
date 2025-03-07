------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection utilities for Fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Reflection where

open import Data.Nat.Base as ℕ hiding (module ℕ)
open import Data.Fin.Base as Fin hiding (module Fin)
open import Data.List.Base using (List; _∷_; []; lookup)
open import Reflection.AST.Term using (Term; con; _⋯⟅∷⟆_)
open import Reflection.AST.Argument using (Arg; _⟨∷⟩_)

------------------------------------------------------------------------
-- Term

toTerm : ∀ {n} → Fin n → Term
toTerm zero    = con (quote Fin.zero) (1 ⋯⟅∷⟆ [])
toTerm (suc i) = con (quote Fin.suc)  (1 ⋯⟅∷⟆ toTerm i ⟨∷⟩ [])

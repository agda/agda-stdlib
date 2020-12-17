------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing finite numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Show where

open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Maybe.Base using (Maybe; nothing; just; _>>=_)
open import Data.Nat as ℕ using (ℕ; _≤?_; _<?_)
import Data.Nat.Show as ℕ
open import Data.String.Base using (String)
open import Function.Base
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True)

show : ∀ {n} → Fin n → String
show = ℕ.show ∘′ toℕ

readMaybe : ∀ {n} base {base≤16 : True (base ≤? 16)} → String → Maybe (Fin n)
readMaybe {n} base {pr} str = do
  nat ← ℕ.readMaybe base {pr} str
  case nat <? n of λ where
    (yes pr) → just (fromℕ< pr)
    (no ¬pr) → nothing

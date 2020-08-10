--------------------------------------------------------------------------------
-- The Agda standard library
--
-- Tactic.Cong.PropEq specialised to operate over one specific type
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat
open import Level
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
import Tactic.Cong.PropEq
open import Tactic.Cong.Common

module Tactic.Cong.PropEq.ForOneType
  (recursion-limit : ℕ)
  {a : Level}
  {A : Set a}
  (_<_ : A → A → Set a)
  (≡-<-trans : Trans {A = A} {B = A} {C = A} _≡_ _<_ _<_)
  where

open Tactic.Cong.PropEq 0 ⊤ω (constω a) (constω A) _<_ ≡-<-trans public

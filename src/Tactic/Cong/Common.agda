------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions commonly used with Tactic.Cong
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.Cong.Common where

open import Level
open import Reflection
open import Data.Unit
open import Reflection.Apply 64
open import Function.Base

⌞_⌟ : ∀ {ℓ} {A : Set ℓ} → A → A
⌞ a ⌟ = a

{-# NOINLINE ⌞_⌟ #-}

data RelSide : Set where
  lhs : RelSide
  rhs : RelSide

record ⊤ω : Setω where
  constructor tt

record ℓSet : Setω where
  constructor _,_
  field
    projₗ : Level
    projₛ : Set projₗ
open ℓSet public

constω : ∀ {b} {A : Setω} {B : Set b} → B → A → B
constω v _ = v

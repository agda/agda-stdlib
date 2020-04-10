------------------------------------------------------------------------
-- The Agda standard library
--
-- Version of id used to annotate expressions for use with Tactic.Cong
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.Cong.Id where

open import Level

⌊_⌋ : ∀ {ℓ} {A : Set ℓ} → A → A
⌊ a ⌋ = a

{-# NOINLINE ⌊_⌋ #-}

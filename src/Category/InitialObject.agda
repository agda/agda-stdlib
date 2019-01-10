------------------------------------------------------------------------
-- The Agda standard library
--
-- Initial objects
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Category.Category

module Category.InitialObject {ℓ} (cat : Category ℓ) where

open Category cat
open import Level

record RawInitial : Set (suc ℓ) where
  field
    Universal    : Obj
    universality : ∀ X → Universal ⇒ X

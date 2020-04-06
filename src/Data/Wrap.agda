------------------------------------------------------------------------
-- The Agda standard library
--
-- Turn a relation into a record definition so as to remember the things
-- being related.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Wrap where

open import Data.Nat
open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Level using (Level)
open import Relation.Nary

private
  variable
    ℓ : Level

record Wrap-inner {n} {ls} {A : Sets n ls} (F : A ⇉ Set ℓ) (xs : Product n A)
                  : Set ℓ where
  constructor mk
  field
    get : uncurryₙ n F xs

open Wrap-inner public

Wrap : ∀ {n ls} {A : Sets n ls} → A ⇉ Set ℓ → A ⇉ Set ℓ
Wrap {n = n} F = curryₙ n (Wrap-inner F)

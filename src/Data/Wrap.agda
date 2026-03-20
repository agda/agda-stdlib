------------------------------------------------------------------------
-- The Agda standard library
--
-- Turn a relation into a record definition so as to remember the things
-- being related.
-- This module has a readme file: README.Data.Wrap
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Wrap where

open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Level using (Level)
open import Relation.Nary

private
  variable
    ℓ : Level

record Wrap′ {n} {ls} {A : Sets n ls} (F : A ⇉ Set ℓ) (xs : Product n A)
                  : Set ℓ where
  constructor [_]
  field
    get : uncurryₙ n F xs

open Wrap′ public

Wrap : ∀ {n ls} {A : Sets n ls} → A ⇉ Set ℓ → A ⇉ Set ℓ
Wrap {n = n} F = curryₙ n (Wrap′ F)

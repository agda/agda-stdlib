------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans: conjunction and disjunction of lists
--
-- Issue #2553: this is a compatibility stub module,
-- ahead of a more thorough refactoring in terms of
-- `Data.List.Effectful.Foldable.foldmap`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool.ListAction where

open import Data.Bool.Base using (Bool; _∧_; _∨_; true; false)
open import Data.List.Base using (List; map; foldr)
open import Function.Base using (_∘_)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a


------------------------------------------------------------------------
-- Definitions

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : (A → Bool) → List A → Bool
any p = or ∘ map p

all : (A → Bool) → List A → Bool
all p = and ∘ map p


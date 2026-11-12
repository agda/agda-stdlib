------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans: conjunction and disjunction of lists
--
-- Refactored in terms of `Data.List.Effectful.Foldable.foldmap`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool.ListAction where

open import Algebra.Bundles using (Monoid)
open import Data.Bool.Base using (Bool)
open import Data.Bool.Properties using (∧-monoid; ∨-monoid)
open import Data.List.Base using (List)
open import Data.List.Effectful.Foldable using (foldMap)
open import Function.Base using (id)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a


------------------------------------------------------------------------
-- Definitions

any : (A → Bool) → List A → Bool
any = foldMap rawMonoid
  where open Monoid ∨-monoid using (rawMonoid)

all : (A → Bool) → List A → Bool
all = foldMap rawMonoid
  where open Monoid ∧-monoid using (rawMonoid)

and : List Bool → Bool
and = all id

or : List Bool → Bool
or = any id


------------------------------------------------------------------------
-- The Agda standard library
--
-- The predicate of being able to decide `null`ity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Null where

open import Data.Bool.Base using (Bool; not; T)
open import Data.Bool.Properties using (T?)
open import Function.Base using (_∘_)
open import Level
open import Relation.Unary using (Pred; Decidable)
open import Relation.Unary.Refinement

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

record Null (A : Set a) : Set a where

  field

    null : A → Bool

  non-null = not ∘ null

------------------------------------------------------------------------
-- Type constructor

[_]⁺ : (A : Set a) {{nullA : Null A}} → Set a
[ A ]⁺ {{nullA}} = [ x ∈ A |ᵇ non-null x ] where open Null nullA

------------------------------------------------------------------------
-- Derived notions

module _ {{nullA : Null A}} where

  open Null nullA

  NonNull : Pred A _
  NonNull = T ∘ non-null

  NonNull? : Decidable NonNull
  NonNull? = T? ∘ non-null

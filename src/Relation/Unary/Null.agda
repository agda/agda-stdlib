------------------------------------------------------------------------
-- The Agda standard library
--
-- The predicate of being able to decide `null`ity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Null where

open import Data.Bool.Base using (Bool; not; T)
open import Function.Base using (_∘_)
open import Level
open import Relation.Unary using (Pred)
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

  not-null = not ∘ null

NonNull : {{Null A}} → Pred A _
NonNull {{nullA}} = T ∘ not-null where open Null nullA

[_]⁺ : (A : Set a) → {{nA : Null A}} → Set a
[ A ]⁺ {{nullA}} =  [ x ∈ A || not-null x ] where open Null nullA


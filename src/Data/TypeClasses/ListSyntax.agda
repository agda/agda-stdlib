------------------------------------------------------------------------
-- The Agda standard library
--
-- A type-class providing list-like syntax for constructing members
-- of the class.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.TypeClasses.ListSyntax where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Recursive.Base using (_^_)
open import Level using (Level; _⊔_)

private
  variable
    a c : Level

------------------------------------------------------------------------
-- Definition

-- Type-class for any type that can be constructed using the list-like
-- syntax `[ x , y , z ]`.
record HasSizedListSyntax (A : Set a) (C : ℕ → Set c) : Set (a ⊔ c) where
  constructor hasListSyntax
  field
    [_] : ∀ {n} → A ^ (suc n) → C (suc n)

-- A synonym for `HasSizedListSyntax` for types that do not track their
-- size (such as `List` itself).
HasListSyntax :(A : Set a) (C : Set c) → Set (a ⊔ c)
HasListSyntax A C = HasSizedListSyntax A (λ _ → C)

open HasSizedListSyntax {{...}} public

------------------------------------------------------------------------
-- Dependencies

-- The constructor for `Data.Product` is needed for this to work so
-- re-export it publicly.

open import Data.Product public
  using (_,_)

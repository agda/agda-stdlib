------------------------------------------------------------------------
-- The Agda standard library
--
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

-- The idea underlying Induction.* comes from Epigram 1, see Section 4
-- of "The view from the left" by McBride and McKinna.

-- Note: The types in this module can perhaps be easier to understand
-- if they are normalised. Note also that Agda can do the
-- normalisation for you.

{-# OPTIONS --cubical-compatible --safe #-}

module Induction where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    Q : Pred A ℓ
    Rec : PT A A ℓ₁ ℓ₂


------------------------------------------------------------------------
-- A RecStruct describes the allowed structure of recursion. The
-- examples in Data.Nat.Induction should explain what this is all
-- about.

RecStruct : Set a → (ℓ₁ ℓ₂ : Level) → Set _
RecStruct A = PT A A

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : RecStruct A ℓ₁ ℓ₂ → Set _
RecursorBuilder Rec = ∀ P → Rec P ⊆′ P → Universal (Rec P)

-- A recursor can be used to actually compute/prove something useful.

Recursor : RecStruct A ℓ₁ ℓ₂ → Set _
Recursor Rec = ∀ P → Rec P ⊆′ P → Universal P

-- And recursors can be constructed from recursor builders.

build : RecursorBuilder Rec → Recursor Rec
build builder P f x = f x (builder P f x)

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : Pred A ℓ → RecStruct A ℓ₁ ℓ₂ → Set _
SubsetRecursorBuilder Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ Rec P

SubsetRecursor : Pred A ℓ → RecStruct A ℓ₁ ℓ₂ → Set _
SubsetRecursor Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ P

subsetBuild : SubsetRecursorBuilder Q Rec → SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)

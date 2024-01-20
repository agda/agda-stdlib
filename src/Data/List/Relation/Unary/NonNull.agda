------------------------------------------------------------------------
-- The Agda standard library
--
-- The `NonNull` predicate, on the model of `Data.Nat.Base.NonZero`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.NonNull where

open import Level using (Level)
open import Data.Bool.Base using (not; T)
open import Data.List.Base using (List; []; _∷_; null; length)
open import Data.Nat.Base as ℕ using (ℕ; _>_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≢_; refl)
open import Relation.Nullary.Negation.Core using (contradiction)


private
  variable
    a : Level
    A : Set a
    x  : A
    xs : List A

------------------------------------------------------------------------
-- Definition

record NonNull {A : Set a} (xs : List A) : Set a where
  field
    nonNull : T (not (null xs))

-- Instances

instance
  nonNull : NonNull (x ∷ xs)
  nonNull = _

-- Constructors

≢-nonNull : xs ≢ [] → NonNull xs
≢-nonNull {xs = []}    []≢[] = contradiction refl []≢[]
≢-nonNull {xs = _ ∷ _} xs≢[] = _

>-nonNull : length xs > 0 → NonNull xs
>-nonNull {xs = _ ∷ _} _ = _

-- Destructors

≢-nonNull⁻¹ : .{{NonNull xs}} → xs ≢ []
≢-nonNull⁻¹ {xs = _ ∷ _} ()

nonNull⇒nonZero : (xs : List A) → .{{NonNull xs}} → ℕ.NonZero (length xs)
nonNull⇒nonZero xs@(_ ∷ _) = _

>-nonNull⁻¹ : (xs : List A) → .{{NonNull xs}} → length xs > 0
>-nonNull⁻¹ xs = ℕ.>-nonZero⁻¹ _ where instance _ = nonNull⇒nonZero xs

-- Specimen uses

nonNull-head : ∀ xs → .{{NonNull xs}} → A
nonNull-head xs@(y ∷ _)  = y

nonNull-tail : ∀ xs → .{{NonNull xs}} → List A
nonNull-tail xs@(_ ∷ ys) = ys

------------------------------------------------------------------------
-- The Agda standard library
--
-- Null instance for List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Null where

open import Data.Nat.Base as Nat using (_>_; z<s)
open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.Product.Base using (∃₂; _,_)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary.Null
open import Relation.Unary.Refinement

private
  variable
    a  : Level
    A  : Set a
    x  : A
    xs : List A


------------------------------------------------------------------------
-- Instance

instance
  nullList : Null (List A)
  nullList = record { null = List.null }

------------------------------------------------------------------------
-- NonNull

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

≢-nonNull⁻¹ : (xs : List A) → .{{NonNull xs}} → xs ≢ []
≢-nonNull⁻¹ (_ ∷ _) ()

>-nonNull⁻¹ : (xs : List A) → .{{NonNull xs}} → length xs > 0
>-nonNull⁻¹ (_ ∷ _) = z<s

-- Existentials

nonNull-[_]⁻ : (xs : List A) → .{{NonNull xs}} → ∃₂ λ y ys → xs ≡ y ∷ ys
nonNull-[ x ∷ xs ]⁻ = x , xs , refl

[_]⁻ : (r : [ List A ]⁺) → ∃₂ λ y ys → refine⁻ r ≡ y ∷ ys
[ refine⁺ xs ]⁻ = nonNull-[ xs ]⁻

-- Smart constructor

_∷⁺_ : A → List A → [ List A ]⁺
_∷⁺_ x xs = refine⁺ (x ∷ xs) {{_}} where instance _ = nonNull


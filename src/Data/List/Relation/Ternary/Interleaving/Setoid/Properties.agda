------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of interleaving using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Ternary.Interleaving.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; []; _∷_; filter; _++_)
open import Data.Bool.Base using (true; false)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (does)
open import Relation.Nullary.Negation using (¬?)
open import Function

open import Data.List.Relation.Binary.Equality.Setoid S using (≋-refl)
open import Data.List.Relation.Ternary.Interleaving.Setoid S
open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Re-exporting existing properties

open import Data.List.Relation.Ternary.Interleaving.Properties public

------------------------------------------------------------------------
-- _++_

++-linear : (xs ys : List A) → Interleaving xs ys (xs ++ ys)
++-linear xs ys = ++-disjoint (left ≋-refl) (right ≋-refl)

------------------------------------------------------------------------
-- filter

module _ {p} {P : A → Set p} (P? : Decidable P) where

  filter⁺ : ∀ xs → Interleaving (filter P? xs) (filter (¬? ∘ P?) xs) xs
  filter⁺ []       = []
  filter⁺ (x ∷ xs) with does (P? x)
  ... | true  = refl ∷ˡ filter⁺ xs
  ... | false = refl ∷ʳ filter⁺ xs

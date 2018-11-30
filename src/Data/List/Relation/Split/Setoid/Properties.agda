------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list-splitting using a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Split.Setoid.Properties {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; []; _∷_; filter)
open import Relation.Unary using (Decidable)
open import Data.List.Relation.Split.Setoid S
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Function

private module S = Setoid S renaming (Carrier to A); open S

-- re-exporting the properties
open import Data.List.Relation.Split.Properties public


module _ {p} {P : A → Set p} (P? : Decidable P) where

  filter⁺ : ∀ xs → Split xs (filter P? xs) (filter (¬? ∘ P?) xs)
  filter⁺ []       = []
  filter⁺ (x ∷ xs) with P? x
  ... | yes px = refl ∷ˡ filter⁺ xs
  ... | no ¬px = refl ∷ʳ filter⁺ xs

------------------------------------------------------------------------
-- The Agda standard library
--
-- Pairs of lists that share no common elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Disjoint.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.List using (List; []; [_]; _∷_)
open import Data.List.Any using (here; there)
open import Data.Product using (_×_; _,_)

open Setoid S renaming (Carrier to A)
open import Data.List.Membership.Setoid S using (_∈_; _∉_)

------------------------------------------------------------------------
-- Definition

Disjoint : Rel (List A) (ℓ ⊔ c)
Disjoint xs ys = ∀ {v} → ¬ (v ∈ xs × v ∈ ys)

------------------------------------------------------------------------
-- Operations

contractₗ : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint xs ys
contractₗ x∷xs∩ys=∅ (v∈xs , v∈ys) = x∷xs∩ys=∅ (there v∈xs , v∈ys)

contractᵣ : ∀ {xs y ys} → Disjoint xs (y ∷ ys) → Disjoint xs ys
contractᵣ xs#y∷ys (v∈xs , v∈ys) = xs#y∷ys (v∈xs , there v∈ys)

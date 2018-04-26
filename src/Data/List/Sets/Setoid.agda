------------------------------------------------------------------------
-- The Agda standard library
--
-- The set interface over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Sets.Setoid  {c ℓ} (S : Setoid c ℓ) where

open import Level
open import Data.List
open import Data.List.Membership.Setoid S public
open import Data.List.Any using (Any; here; there)
open import Data.List.All

open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊈_ _⊆′_ _⊈′_

_⊆_ : Rel (List A) _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : Rel (List A) _
xs ⊈ ys = ¬ xs ⊆ ys

_⊆′_ : Rel (List A) _
xs ⊆′ ys = All (_∈ ys) xs

_⊈′_ : Rel (List A) _
l₁ ⊈′ l₂ = ¬ (l₁ ⊆′ l₂)

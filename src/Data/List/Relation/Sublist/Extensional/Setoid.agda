------------------------------------------------------------------------
-- The Agda standard library
--
-- The extensional sublist relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Sublist.Extensional.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Data.Bool using (Bool; true; false)
open import Data.List
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Properties using (map↔)
open import Data.List.Membership.Setoid S
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Equality.Setoid S
open import Data.Product as Prod using ()
open import Function using (_∘_; _∘′_; id)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊈_

_⊆_ : List A → List A → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : List A → List A → Set _
xs ⊈ ys = ¬ xs ⊆ ys

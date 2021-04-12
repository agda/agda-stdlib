------------------------------------------------------------------------
-- The Agda standard library
--
-- The extensional sublist relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Subset.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Setoid S using (_∈_)
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)
open import Function.Base using (flip)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Any using (here; there)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊇_ _⊈_ _⊉_

_⊆_ : Rel (List A) (c ⊔ ℓ)
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊇_ : Rel (List A) (c ⊔ ℓ)
_⊇_ = flip _⊆_

_⊈_ : Rel (List A) (c ⊔ ℓ)
xs ⊈ ys = ¬ xs ⊆ ys

_⊉_ : Rel (List A) (c ⊔ ℓ)
xs ⊉ ys = ¬ xs ⊇ ys


infixr 3 _|>_

_|>_ : ∀ {xs ys x} → x ∈ ys → xs ⊆ ys → x ∷ xs ⊆ ys
_|>_ x∈ys _  (here x-refl) = ∈-resp-≈ S (sym x-refl) x∈ys
_|>_ _ xs⊆ys (there x∈xs) = xs⊆ys x∈xs

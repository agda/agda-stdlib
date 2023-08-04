------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Covec type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Covec.Properties where

open import Size
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Conat
open import Codata.Sized.Covec
open import Codata.Sized.Covec.Bisimilarity
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core as Eq

-- Functor laws

module _ {a} {A : Set a} where

 map-id : ∀ {m} (as : Covec A ∞ m) {i} → i , m ⊢ map id as ≈ as
 map-id []       = []
 map-id (a ∷ as) = Eq.refl ∷ λ where .force → map-id (as .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 map-∘ : ∀ (f : A → B) (g : B → C) {m} as {i} → i , m ⊢ map g (map f as) ≈ map (g ∘ f) as
 map-∘ f g []       = []
 map-∘ f g (a ∷ as) = Eq.refl ∷ λ where .force → map-∘ f g (as .force)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-identity = map-id
{-# WARNING_ON_USAGE map-identity
"Warning: map-identity was deprecated in v2.0.
Please use map-id instead."
#-}

map-map-fusion = map-∘
{-# WARNING_ON_USAGE map-map-fusion
"Warning: map-map-fusion was deprecated in v2.0.
Please use map-∘ instead."
#-}

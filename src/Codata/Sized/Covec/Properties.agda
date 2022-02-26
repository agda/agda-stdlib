------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Covec type
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Sized.Covec.Properties where

open import Size
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Conat
open import Codata.Sized.Covec
open import Codata.Sized.Covec.Bisimilarity
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq

-- Functor laws

module _ {a} {A : Set a} where

 map-identity : ∀ {m} (as : Covec A ∞ m) {i} → i , m ⊢ map id as ≈ as
 map-identity []       = []
 map-identity (a ∷ as) = Eq.refl ∷ λ where .force → map-identity (as .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 map-map-fusion : ∀ (f : A → B) (g : B → C) {m} as {i} → i , m ⊢ map g (map f as) ≈ map (g ∘ f) as
 map-map-fusion f g []       = []
 map-map-fusion f g (a ∷ as) = Eq.refl ∷ λ where .force → map-map-fusion f g (as .force)

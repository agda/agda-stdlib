------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.All.Properties where

open import Data.Maybe.Base
open import Data.Maybe.All as All using (All; nothing; just)
open import Data.Product using (_×_; _,_)
open import Function
open import Relation.Unary

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for maybe operations
------------------------------------------------------------------------
-- map

module _ {a b p} {A : Set a} {B : Set b} {P : Pred B p} {f : A → B} where

  map⁺ : ∀ {mx} → All (P ∘ f) mx → All P (map f mx)
  map⁺ (just p) = just p
  map⁺ nothing  = nothing

  map⁻ : ∀ {mx} → All P (map f mx) → All (P ∘ f) mx
  map⁻ {just x}  (just px) = just px
  map⁻ {nothing} nothing   = nothing

-- A variant of All.map.

module _ {a b p q} {A : Set a} {B : Set b} {f : A → B}
         {P : Pred A p} {Q : Pred B q} where

  gmap : P ⊆ Q ∘ f → All P ⊆ All Q ∘ map f
  gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- _<∣>_

module _ {a p} {A : Set a} {P : A → Set p} where

  <∣>⁺ : ∀ {mx my} → All P mx → All P my → All P (mx <∣> my)
  <∣>⁺ (just px) pmy = just px
  <∣>⁺ nothing   pmy = pmy

  <∣>⁻ : ∀ mx {my} → All P (mx <∣> my) → All P mx
  <∣>⁻ (just x) pmxy = pmxy
  <∣>⁻ nothing  pmxy = nothing

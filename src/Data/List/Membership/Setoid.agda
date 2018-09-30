------------------------------------------------------------------------
-- The Agda standard library
--
-- List membership and some related definitions
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Function using (_∘_; id; flip)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length; lookup)
open import Data.List.Any using (Any; map; here; there)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _∈_ _∉_

_∈_ : A → List A → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : A → List A → Set _
x ∉ xs = ¬ x ∈ xs

------------------------------------------------------------------------
-- Operations

mapWith∈ : ∀ {b} {B : Set b}
           (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
mapWith∈ []       f = []
mapWith∈ (x ∷ xs) f = f (here refl) ∷ mapWith∈ xs (f ∘ there)

_∷=_ : ∀ {xs x} → x ∈ xs → A → List A
_∷=_ {_ ∷ xs} (here _)   v = v ∷ xs
_∷=_ {x ∷ _}  (there pr) v = x ∷ (pr ∷= v)

infixl 4 _─_
_─_ : ∀ xs {x} → x ∈ xs → List A
_ ∷ xs ─ here px    = xs
x ∷ xs ─ there x∈xs = x ∷ (xs ─ x∈xs)

fromFin : ∀ {xs} (k : Fin (length xs)) → lookup xs k ∈ xs
fromFin {_ ∷ _} zero    = here refl
fromFin {_ ∷ _} (suc k) = there (fromFin k)

find : ∀ {p} {P : A → Set p} {xs} →
       Any P xs → ∃ λ x → x ∈ xs × P x
find (here px)   = (_ , here refl , px)
find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

lose : ∀ {p} {P : A → Set p} {x xs} →
       P Respects _≈_ → x ∈ xs → P x → Any P xs
lose resp x∈xs px = map (flip resp px) x∈xs

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.16

map-with-∈ = mapWith∈
{-# WARNING_ON_USAGE map-with-∈
"Warning: map-with-∈ was deprecated in v0.16.
Please use mapWith∈ instead."
#-}

------------------------------------------------------------------------
-- The Agda standard library
--
-- List membership and some related definitions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any
  using (Any; map; here; there)
open import Data.Product.Base as Product using (∃; _×_; _,_)
open import Function.Base using (_∘_; flip; const)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Pred)

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

_∷=_ = Any._∷=_ {A = A}
_─_ = Any._─_ {A = A}

mapWith∈ : ∀ {b} {B : Set b}
           (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
mapWith∈ []       f = []
mapWith∈ (x ∷ xs) f = f (here refl) ∷ mapWith∈ xs (f ∘ there)

------------------------------------------------------------------------
-- Finding and losing witnesses

module _ {p} {P : Pred A p} where

  find : ∀ {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
  find (here px)   = _ , here refl , px
  find (there pxs) = let x , x∈xs , px = find pxs in x , there x∈xs , px

  lose : P Respects _≈_ →  ∀ {x xs} → x ∈ xs → P x → Any P xs
  lose resp x∈xs px = map (flip resp px) x∈xs

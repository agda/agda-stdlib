------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership of vectors, along with some additional definitions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; _Respects_)

module Data.Vec.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Function
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Any as Any using (Any; here; there; index)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _∈_ _∉_

_∈_ : A → ∀ {n} → Vec A n → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : A → ∀ {n} → Vec A n → Set _
x ∉ xs = ¬ x ∈ xs

------------------------------------------------------------------------
-- Operations

mapWith∈ : ∀ {b} {B : Set b} {n}
           (xs : Vec A n) → (∀ {x} → x ∈ xs → B) → Vec B n
mapWith∈ []       f = []
mapWith∈ (x ∷ xs) f = f (here refl) ∷ mapWith∈ xs (f ∘ there)

_∷=_ : ∀ {n} {xs : Vec A n} {x} → x ∈ xs → A → Vec A n
_∷=_ {xs = xs} x∈xs v = xs Vec.[ index x∈xs ]≔ v

------------------------------------------------------------------------
-- Finding and losing witnesses

module _ {p} {P : Pred A p} where

  find : ∀ {n} {xs : Vec A n} → Any P xs → ∃ λ x → x ∈ xs × P x
  find (here px)   = (_ , here refl , px)
  find (there pxs) with find pxs
  ... | (x , x∈xs , px) = (x , there x∈xs , px)

  lose : P Respects _≈_ → ∀ {x n} {xs : Vec A n} → x ∈ xs → P x → Any P xs
  lose resp x∈xs px = Any.map (flip resp px) x∈xs

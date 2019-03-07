------------------------------------------------------------------------
-- The Agda standard library
--
-- Tables, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Table.Base where

open import Data.Nat
open import Data.Fin
open import Data.Product using (_×_ ; _,_)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)
open import Function using (_∘_; flip)

------------------------------------------------------------------------
-- Type

record Table {a} (A : Set a) n : Set a where
  constructor tabulate
  field lookup : Fin n → A
open Table public

------------------------------------------------------------------------
-- Basic operations

module _ {a} {A : Set a} where

  head : ∀ {n} → Table A (suc n) → A
  head t = lookup t zero

  tail : ∀ {n} → Table A (suc n) → Table A n
  tail t = tabulate (lookup t ∘ suc)

  uncons : ∀ {n} → Table A (suc n) → A × Table A n
  uncons t = head t , tail t

  remove : ∀ {n} → Fin (suc n) → Table A (suc n) → Table A n
  remove i t = tabulate (lookup t ∘ punchIn i)

------------------------------------------------------------------------
-- Operations for transforming tables

module _ {a} {A : Set a} where

  rearrange : ∀ {m n} → (Fin m → Fin n) → Table A n → Table A m
  rearrange f t = tabulate (lookup t ∘ f)

module _ {a b} {A : Set a} {B : Set b} where

  map : ∀ {n} → (A → B) → Table A n → Table B n
  map f t = tabulate (f ∘ lookup t)

  _⊛_ : ∀ {n} → Table (A → B) n → Table A n → Table B n
  fs ⊛ xs = tabulate λ i → lookup fs i (lookup xs i)

------------------------------------------------------------------------
-- Operations for reducing tables

module _ {a b} {A : Set a} {B : Set b} where

  foldr : ∀ {n} → (A → B → B) → B → Table A n → B
  foldr {n = zero}  f z t = z
  foldr {n = suc n} f z t = f (head t) (foldr f z (tail t))

  foldl : ∀ {n} → (B → A → B) → B → Table A n → B
  foldl {n = zero}  f z t = z
  foldl {n = suc n} f z t = foldl f (f z (head t)) (tail t)

------------------------------------------------------------------------
-- Operations for building tables

module _ {a} {A : Set a} where

  replicate : ∀ {n} → A → Table A n
  replicate x = tabulate (λ _ → x)

------------------------------------------------------------------------
-- Operations for converting tables

module _ {a} {A : Set a} where

  toList : ∀ {n} → Table A n → List A
  toList = List.tabulate ∘ lookup

  fromList : ∀ (xs : List A) → Table A (List.length xs)
  fromList = tabulate ∘ List.lookup

  fromVec : ∀ {n} → Vec A n → Table A n
  fromVec = tabulate ∘ Vec.lookup

  toVec : ∀ {n} → Table A n → Vec A n
  toVec = Vec.tabulate ∘ lookup

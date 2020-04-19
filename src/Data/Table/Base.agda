------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Vec.Functional` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Table.Base where

{-# WARNING_ON_IMPORT
"Data.Table.Base was deprecated in v1.2.
Use Data.Vec.Functional instead."
#-}

open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Product using (_×_ ; _,_)
open import Data.List.Base as List using (List)
open import Data.Vec.Base as Vec using (Vec)
open import Function using (_∘_; flip)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

record Table (A : Set a) n : Set a where
  constructor tabulate
  field lookup : Fin n → A
open Table public

------------------------------------------------------------------------
-- Basic operations

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

rearrange : ∀ {m n} → (Fin m → Fin n) → Table A n → Table A m
rearrange f t = tabulate (lookup t ∘ f)

map : ∀ {n} → (A → B) → Table A n → Table B n
map f t = tabulate (f ∘ lookup t)

_⊛_ : ∀ {n} → Table (A → B) n → Table A n → Table B n
fs ⊛ xs = tabulate λ i → lookup fs i (lookup xs i)

------------------------------------------------------------------------
-- Operations for reducing tables

foldr : ∀ {n} → (A → B → B) → B → Table A n → B
foldr {n = zero}  f z t = z
foldr {n = suc n} f z t = f (head t) (foldr f z (tail t))

foldl : ∀ {n} → (B → A → B) → B → Table A n → B
foldl {n = zero}  f z t = z
foldl {n = suc n} f z t = foldl f (f z (head t)) (tail t)

------------------------------------------------------------------------
-- Operations for building tables

replicate : ∀ {n} → A → Table A n
replicate x = tabulate (λ _ → x)

------------------------------------------------------------------------
-- Operations for converting tables

toList : ∀ {n} → Table A n → List A
toList = List.tabulate ∘ lookup

fromList : ∀ (xs : List A) → Table A (List.length xs)
fromList = tabulate ∘ List.lookup

fromVec : ∀ {n} → Vec A n → Table A n
fromVec = tabulate ∘ Vec.lookup

toVec : ∀ {n} → Table A n → Vec A n
toVec = Vec.tabulate ∘ lookup

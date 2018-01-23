------------------------------------------------------------------------
-- The Agda standard library
--
-- Fixed-size tables of values, implemented as functions from 'Fin n'.
-- Similar to 'Data.Vec', but focusing on ease of retrieval instead of
-- ease of adding and removing elements.
------------------------------------------------------------------------

module Data.Table.Core where

open import Data.Fin
open import Data.List as List using (List)
open import Data.Nat using (ℕ)
open import Function using (_∘_)

record Table {a} (A : Set a) n : Set a where
  constructor tabulate
  field
    lookup : Fin n → A

open Table public

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Table A n → Table B n
map f t = tabulate (f ∘ lookup t)


-- A contravariant map over the indices

rearrange : ∀ {a} {A : Set a} {m n} → (Fin m → Fin n) → Table A n → Table A m
rearrange f t = tabulate (lookup t ∘ f)

head : ∀ {n a} {A : Set a} → Table A (ℕ.suc n) → A
head t = lookup t zero

tail : ∀ {n a} {A : Set a} → Table A (ℕ.suc n) → Table A n
tail t = tabulate (lookup t ∘ suc)

toList : ∀ {n a} {A : Set a} → Table A n → List A
toList = List.tabulate ∘ lookup

fromList : ∀ {a} {A : Set a} (xs : List A) → Table A (List.length xs)
fromList = tabulate ∘ List.lookup

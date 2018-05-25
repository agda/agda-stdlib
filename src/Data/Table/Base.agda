------------------------------------------------------------------------
-- The Agda standard library
--
-- Tables, basic types and operations
------------------------------------------------------------------------

module Data.Table.Base where

open import Data.Nat
open import Data.Fin
open import Data.Product using (_×_ ; _,_)
open import Data.List as List using (List)
open import Function using (_∘_)

record Table {a} (A : Set a) n : Set a where
  constructor tabulate
  field lookup : Fin n → A
open Table public

module _ {a} {A : Set a} {n : ℕ} where

-- A contravariant map over the indices

  rearrange : ∀ {m} → (Fin m → Fin n) → Table A n → Table A m
  rearrange f t = tabulate (lookup t ∘ f)

-- List-like combinators

  head : Table A (ℕ.suc n) → A
  head t = lookup t zero

  tail : Table A (ℕ.suc n) → Table A n
  tail t = tabulate (lookup t ∘ suc)

  uncons : Table A (ℕ.suc n) → A × Table A n
  uncons t = head t , tail t

  toList : Table A n → List A
  toList = List.tabulate ∘ lookup

fromList : ∀ {a} {A : Set a} (xs : List A) → Table A (List.length xs)
fromList = tabulate ∘ List.lookup

remove : ∀ {n a} {A : Set a} (i : Fin (suc n)) → Table A (suc n) → Table A n
remove i = rearrange (punchIn i)

module _ {a b} {A : Set a} {B : Set b} where

-- Folds

  foldr : ∀ {n} → (A → B → B) → B → Table A n → B
  foldr {n = zero}  f z t = z
  foldr {n = suc n} f z t = f (head t) (foldr f z (tail t))

  foldl : ∀ {n} → (B → A → B) → B → Table A n → B
  foldl {n = zero}  f z t = z
  foldl {n = suc n} f z t = foldl f (f z (head t)) (tail t)

-- Functor

  map : ∀ {n} → (A → B) → Table A n → Table B n
  map f t = tabulate (f ∘ lookup t)

-- Applicative

replicate : ∀ {n a} {A : Set a} → A → Table A n
replicate x = tabulate (λ _ → x)

_⊛_ : ∀ {n a b} {A : Set a} {B : Set b} → Table (A → B) n → Table A n → Table B n
fs ⊛ xs = tabulate λ i → lookup fs i (lookup xs i)

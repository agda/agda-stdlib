------------------------------------------------------------------------
-- The Agda standard library
--
-- Streams where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Codata.Guarded.Stream.Relation.Unary.Any where

open import Codata.Guarded.Stream as Stream using (Stream)
open import Data.Empty
open import Data.Nat.Base hiding (_⊔_)
open import Level hiding (zero; suc)
open import Relation.Nullary
open import Relation.Unary

private
  variable
    a p q : Level
    A : Set a
    P Q : Pred A p
    xs : Stream A

data Any {A : Set a} (P : Pred A p) : Stream A → Set (a ⊔ p) where
  here  : ∀ {xs} →     P (Stream.head xs) → Any P xs
  there : ∀ {xs} → Any P (Stream.tail xs) → Any P xs

head : ¬ Any P (Stream.tail xs) → Any P xs → P (Stream.head xs)
head ¬t (here h) = h
head ¬t (there t) = ⊥-elim (¬t t)

tail : ¬ P (Stream.head xs) → Any P xs → Any P (Stream.tail xs)
tail ¬h (here h) = ⊥-elim (¬h h)
tail ¬h (there t) = t

map : P ⊆ Q → Any P ⊆ Any Q
map g (here  px ) = here (g px)
map g (there pxs) = there (map g pxs)

index : Any P xs → ℕ
index (here  px ) = zero
index (there pxs) = suc (index pxs)

lookup : {P : Pred A p} → Any P xs → A
lookup {xs = xs} p = Stream.lookup xs (index p)

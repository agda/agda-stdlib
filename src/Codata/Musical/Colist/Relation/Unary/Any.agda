------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists where at least one element satisfies a predicate
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Relation.Unary.Any where

open import Codata.Musical.Colist.Base
open import Codata.Musical.Notation
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∋_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred)

private
  variable
    a b p : Level
    A : Set a
    B : Set b
    P : Pred A p

data Any {A : Set a} (P : Pred A p) : Pred (Colist A) (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)          → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P (♭ xs)) → Any P (x ∷ xs)

index : ∀ {xs} → Any P xs → ℕ
index (here px) = zero
index (there p) = suc (index p)

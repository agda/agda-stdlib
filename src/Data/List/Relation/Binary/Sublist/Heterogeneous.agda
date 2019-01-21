------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous sublist relation
-- This is a generalisation of what is commonly known as Order
-- Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Heterogeneous where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Type and basic combinators

module _ {a b r} {A : Set a} {B : Set b} (R : REL A B r) where

  data Sublist : REL (List A) (List B) (a ⊔ b ⊔ r) where
    []   : Sublist [] []
    _∷ʳ_ : ∀ {xs ys} → ∀ y → Sublist xs ys → Sublist xs (y ∷ ys)
    _∷_  : ∀ {x xs y ys} → R x y → Sublist xs ys → Sublist (x ∷ xs) (y ∷ ys)

module _ {a b r s} {A : Set a} {B : Set b} {R : REL A B r} {S : REL A B s} where

  map : R ⇒ S → Sublist R ⇒ Sublist S
  map f []        = []
  map f (y ∷ʳ rs) = y ∷ʳ map f rs
  map f (r ∷ rs)  = f r ∷ map f rs

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  minimum : Min (Sublist R) []
  minimum []       = []
  minimum (x ∷ xs) = x ∷ʳ minimum xs

------------------------------------------------------------------------
-- Conversion to and from Any

  toAny : ∀ {a bs} → Sublist R [ a ] bs → Any (R a) bs
  toAny (y ∷ʳ rs) = there (toAny rs)
  toAny (r ∷ rs)  = here r

  fromAny : ∀ {a bs} → Any (R a) bs → Sublist R [ a ] bs
  fromAny (here r)  = r ∷ minimum _
  fromAny (there p) = _ ∷ʳ fromAny p

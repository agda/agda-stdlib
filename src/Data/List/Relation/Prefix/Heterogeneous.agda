------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous prefix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Prefix.Heterogeneous where

open import Level
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (∃; _×_; _,_; uncurry)
open import Relation.Binary using (REL; _⇒_)

module _ {a b r} {A : Set a} {B : Set b} (R : REL A B r) where

  data Prefix : REL (List A) (List B) (a ⊔ b ⊔ r) where
    []  : ∀ {bs} → Prefix [] bs
    _∷_ : ∀ {a b as bs} → R a b → Prefix as bs → Prefix (a ∷ as) (b ∷ bs)

  data PrefixView (as : List A) : List B → Set (a ⊔ b ⊔ r) where
    _++_ : ∀ {cs} → Pointwise R as cs → ∀ ds → PrefixView as (cs List.++ ds)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} {a b as bs} where

  head : Prefix R (a ∷ as) (b ∷ bs) → R a b
  head (r ∷ rs) = r

  tail : Prefix R (a ∷ as) (b ∷ bs) → Prefix R as bs
  tail (r ∷ rs) = rs

  uncons : Prefix R (a ∷ as) (b ∷ bs) → R a b × Prefix R as bs
  uncons (r ∷ rs) = r , rs

module _ {a b r s} {A : Set a} {B : Set b} {R : REL A B r} {S : REL A B s} where

  map : R ⇒ S → Prefix R ⇒ Prefix S
  map R⇒S []       = []
  map R⇒S (r ∷ rs) = R⇒S r ∷ map R⇒S rs

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  toView : ∀ {as bs} → Prefix R as bs → PrefixView R as bs
  toView []       = [] ++ _
  toView (r ∷ rs) with toView rs
  ... | rs′ ++ ds = (r ∷ rs′) ++ ds

  fromView : ∀ {as bs} → PrefixView R as bs → Prefix R as bs
  fromView ([]       ++ ds) = []
  fromView ((r ∷ rs) ++ ds) = r ∷ fromView (rs ++ ds)

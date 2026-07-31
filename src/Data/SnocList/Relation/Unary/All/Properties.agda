------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of All<
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.SnocList.Relation.Unary.All.Properties where

open import Data.List.Relation.Unary.All using (All; [])
open import Data.SnocList.Base using (_<>>_; List<; List>; _:>_; _<:_; toList>; [])
open import Data.SnocList.Relation.Unary.All using (All<; _<:_; Null<)
open import Level using (Level)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properites of All<

all<>> : ∀ {x} {xs : List< A} {ys : List> A} {p : Pred A a} → All p ys → All< p xs → p x → All p (xs <>> (x :> ys))
all<>> {xs = []} allys allxs px = px All.∷ allys
all<>> {x = a} {xs = xs <: x} {ys = ys} allys (px <: allxs) pa = all<>> (pa All.∷ allys) allxs px

all<> : ∀ {xs : List< A} {p : Pred A a} → All< p xs → All p (toList> xs)
all<> {xs = []} all< = []
all<> {xs = xs <: x} (px <: all<) = all<>> [] all< px

------------------------------------------------------------------------
-- Properites of Null<

null-<: : {a : A} {as : List< A} → ¬ (Null< (as <: a))
null-<: (() Data.SnocList.Relation.Unary.All.<: n)

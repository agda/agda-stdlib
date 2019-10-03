------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of All predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.All.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘′_)
open import Relation.Nullary
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)
open import Data.List.Fresh.Relation.Unary.All

private
  variable
    a p r : Level
    A : Set a

module _ {R : Rel A r} where

  fromAll : ∀ {x} {xs : List# A R} → All (R x) xs → x # xs
  fromAll []       = _
  fromAll (p ∷ ps) = p , fromAll ps

  toAll : ∀ {x} {xs : List# A R} → x # xs → All (R x) xs
  toAll {xs = []}      _        = []
  toAll {xs = a ∷# as} (p , ps) = p ∷ toAll ps

module _ {R : Rel A r} {P : Pred A p} where

  append⁺ : {xs ys : List# A R} {ps : All (_# ys) xs} →
            All P xs → All P ys → All P (append xs ys ps)
  append⁺ []         pys = pys
  append⁺ (px ∷ pxs) pys = px ∷ append⁺ pxs pys

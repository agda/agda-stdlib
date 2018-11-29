------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector's Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Any.Properties where

open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_; lookup; toList; fromList)
open import Data.Vec.Any
open import Data.List.Any as List using (here; there)
open import Relation.Unary

module _ {a} {A : Set a} {p} {P : Pred A p} where

  lookup-index : ∀ {m} {xs : Vec A m} (p : Any P xs) → P (lookup (index p) xs)
  lookup-index (here px) = px
  lookup-index (there p) = lookup-index p

  fromList⁺ : ∀ {xs} → List.Any P xs → Any P (fromList xs)
  fromList⁺ (here px) = here px
  fromList⁺ (there v) = there (fromList⁺ v)

  fromList⁻ : ∀ {xs} → Any P (fromList xs) → List.Any P xs
  fromList⁻ {[]}     ()
  fromList⁻ {x ∷ xs} (here px)   = here px
  fromList⁻ {x ∷ xs} (there pxs) = there (fromList⁻ pxs)

  toList⁺ : ∀ {n} {xs : Vec A n} → Any P xs → List.Any P (toList xs)
  toList⁺ (here px) = here px
  toList⁺ (there v) = there (toList⁺ v)

  toList⁻ : ∀ {n} {xs : Vec A n} → List.Any P (toList xs) → Any P xs
  toList⁻ {xs = []}     ()
  toList⁻ {xs = x ∷ xs} (here px)   = here px
  toList⁻ {xs = x ∷ xs} (there pxs) = there (toList⁻ pxs)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Streams where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Codata.Guarded.Stream.Relation.Unary.All where

open import Codata.Guarded.Stream using (Stream; head; tail)
open import Data.Product using (_,_; proj₁; proj₂)
open import Level
open import Relation.Unary

private
  variable
    a p ℓ : Level
    A : Set a
    P Q R : Pred A p
    xs : Stream A

infixr 5 _∷_

record All (P : Pred A ℓ) (as : Stream A) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head :     P (head as)
    tail : All P (tail as)

open All public

map : P ⊆ Q → All P ⊆ All Q
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

zipWith : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
head (zipWith f (ps , qs)) = f (head ps , head qs)
tail (zipWith f (ps , qs)) = zipWith f (tail ps , tail qs)

unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q
head (proj₁ (unzipWith f rs)) = proj₁ (f (head rs))
tail (proj₁ (unzipWith f rs)) = proj₁ (unzipWith f (tail rs))
head (proj₂ (unzipWith f rs)) = proj₂ (f (head rs))
tail (proj₂ (unzipWith f rs)) = proj₂ (unzipWith f (tail rs))

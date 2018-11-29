------------------------------------------------------------------------
-- The Agda standard library
--
-- List-splitting using a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Split.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise as Pw
open import Data.List.Relation.Split.Properties
private module S = Setoid S renaming (Carrier to A); open S

-- re-exporting the basic combinators
open import Data.List.Relation.Split as Split hiding (Split) public

-- defining a specialised version of the datatype
Split : List A → List A → List A → Set (c ⊔ ℓ)
Split = Split.Split _≈_ _≈_

_++_ : (xs ys : List A) → Split (xs List.++ ys) xs ys
xs ++ ys = disjoint (Split.left (Pw.refl S.refl)) (Split.right (Pw.refl S.refl))

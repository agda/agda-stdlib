------------------------------------------------------------------------
-- The Agda standard library
--
-- List-splitting using a setoid
------------------------------------------------------------------------

open import Relation.Binary using (Setoid)

module Data.List.Relation.Split.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise as Pw
open import Data.List.Relation.Split
open import Data.List.Relation.Split.Properties
private module S = Setoid S renaming (Carrier to A); open S

Interleaving : List A → List A → List A → Set ℓ
Interleaving = Split _≈_ _≈_

_++_ : (xs ys : List A) → Interleaving (xs List.++ ys) xs ys
xs ++ ys = disjoint (left (Pw.refl S.refl)) (right (Pw.refl S.refl))

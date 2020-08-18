------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid)

module Data.Vec.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.Vec.Base
import Data.Vec.Relation.Unary.AllPairs as AllPairsM
open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)


------------------------------------------------------------------------
-- Definition

private
  Distinct : Rel A ℓ
  Distinct x y = ¬ (x ≈ y)

open import Data.Vec.Relation.Unary.AllPairs.Core Distinct public
     renaming (AllPairs to Unique)

open import Data.Vec.Relation.Unary.AllPairs {R = Distinct} public
     using (head; tail)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid)

module Data.List.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.List
import Data.List.Relation.Unary.AllPairs as AllPairsM
open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)


------------------------------------------------------------------------
-- Definition

private

  Distinct : Rel A ℓ
  Distinct x y = ¬ (x ≈ y)

open import Data.List.Relation.Unary.AllPairs.Core Distinct
     renaming (AllPairs to Unique)
     public

open import Data.List.Relation.Unary.AllPairs {R = Distinct}
     using (head; tail)
     public

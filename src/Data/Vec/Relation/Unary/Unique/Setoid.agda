------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)

module Data.Vec.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.Vec.Base
import Data.Vec.Relation.Unary.AllPairs as AllPairsM
open import Level using (_⊔_)
import Relation.Binary.Definitions as B
open import Relation.Unary as U using (Pred)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable.Core using (¬?)


------------------------------------------------------------------------
-- Definition

private
  Distinct : Rel A ℓ
  Distinct x y = ¬ (x ≈ y)

open import Data.Vec.Relation.Unary.AllPairs.Core Distinct public
     renaming (AllPairs to Unique)

open import Data.Vec.Relation.Unary.AllPairs {R = Distinct} public
     using (head; tail)

unique? : ∀ {n} → B.Decidable _≈_ → U.Decidable (Unique {n})
unique? _≈?_ = AllPairsM.allPairs? λ x y → ¬? (x ≈? y)

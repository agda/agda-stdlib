------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance for Strings
-- We include both the case sensitive and insensitive versions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Text.Distance.Levenshtein where

open import Data.Char.Base as Char using (Char)
import Data.Char.Properties as Charₚ
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.String.Base using (String; toList)

module CaseSensitive where

  import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Propositional Char as Edit
  import Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid Charₚ.setoid as Dist
  import Data.List.Relation.Binary.Distance.Levenshtein.Calc.DecPropositional Charₚ._≡?_ as Calc

  open Dist using (Dist)

  distance : String → String → ℕ
  distance xs ys = proj₁ (Calc.compute (toList xs) (toList ys))

  record _≈[_]_ (xs : String) (k : ℕ) (ys : String) : Set where
    field isDist : Dist (toList xs) (toList ys) k
  open _≈[_]_ public

  caseSensitive : (xs ys : String) → xs ≈[ distance xs ys ] ys
  caseSensitive xs ys .isDist = proj₂ (Calc.compute (toList xs) (toList ys))

open CaseSensitive using (_≈[_]_; caseSensitive) public


module CaseInsensitive where

  open import Relation.Binary.Bundles using (Setoid; DecSetoid)
  import Relation.Binary.Construct.On as On

  -- should this go in Data.Char?
  setoid : Setoid _ _
  setoid = On.setoid Charₚ.setoid Char.toLower

  decSetoid : DecSetoid _ _
  decSetoid = On.decSetoid Charₚ.decSetoid Char.toLower

  import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Setoid setoid as Edit
  import Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid setoid as Dist
  import Data.List.Relation.Binary.Distance.Levenshtein.Calc.DecSetoid decSetoid as Calc

  open Dist using (Dist)

  distance : String → String → ℕ
  distance xs ys = proj₁ (Calc.compute (toList xs) (toList ys))

  record _≋[_]_ (xs : String) (k : ℕ) (ys : String) : Set where
    field isDist : Dist (toList xs) (toList ys) k
  open _≋[_]_ public

  caseInsensitive : (xs ys : String) → xs ≋[ distance xs ys ] ys
  caseInsensitive xs ys .isDist = proj₂ (Calc.compute (toList xs) (toList ys))

open CaseInsensitive using (_≋[_]_; caseInsensitive) public


-- Examples

_ : "banana" ≈[ 2 ] "Canada"
_ = caseSensitive _ _

_ : "Agda" ≈[ 3 ] "aGdA"
_ = caseSensitive _ _

_ : "Agda" ≋[ 0 ] "aGdA"
_ = caseInsensitive _ _

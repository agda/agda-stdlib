------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: calculations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Distance.Levenshtein.Calc.DecPropositional
  {a} {A : Set a} (_≡?_ : DecidableEquality A) where

open import Data.List.Base
  using ()
  renaming (List to List>)
open import Data.Product.Base using (∃)

open import Relation.Binary.PropositionalEquality using (setoid; decSetoid)

open import Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid (setoid A)
import Data.List.Relation.Binary.Distance.Levenshtein.Calc.DecSetoid (decSetoid _≡?_) as S

compute : (xs ys : List> A) → ∃ (Dist xs ys)
compute = S.compute

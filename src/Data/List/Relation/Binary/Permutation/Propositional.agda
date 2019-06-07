------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Setoid as SetoidPermutations
open import Data.List.Relation.Binary.Equality.Propositional using (≋-refl)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- An inductive definition of permutation

private
  module Permutations = SetoidPermutations (setoid A)

open Permutations public
  -- hiding (prep; swap)

-- Redefine the `prep` and `swap` predicates so they don't require
-- equality proofs

{-
pattern prep x ↭   = Permutations.prep (P.refl {x = x}) ↭
pattern swap x y ↭ = Permutations.swap (P.refl {x = x}) (P.refl {x = y}) ↭
-}

------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation for types which have a
-- decidable equality. This is commonly known as Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Decidable)
open import Agda.Builtin.Equality using (_≡_)

module Data.List.Relation.Binary.Sublist.DecPropositional
       {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_)
       where

import Relation.Binary.PropositionalEquality as P

open import Data.List.Relation.Binary.Sublist.DecSetoid (P.decSetoid _≟_)
  hiding (lookup) public
open import Data.List.Relation.Binary.Sublist.Propositional {A = A}
  using (lookup) public

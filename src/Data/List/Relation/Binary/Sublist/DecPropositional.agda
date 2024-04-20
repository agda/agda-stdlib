------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation for types which have
-- a decidable equality. This is commonly known as Order Preserving
-- Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Sublist.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A)
  where

open import Data.List.Relation.Binary.Equality.DecPropositional _≟_
  using (_≡?_)
import Data.List.Relation.Binary.Sublist.DecSetoid as DecSetoidSublist
import Data.List.Relation.Binary.Sublist.Propositional as PropositionalSublist
open import Relation.Binary.Bundles using (DecPoset)
open import Relation.Binary.Structures using (IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Re-export core definitions and operations

open PropositionalSublist {A = A} public
open DecSetoidSublist (decSetoid _≟_) using (_⊆?_) public

------------------------------------------------------------------------
-- Additional relational properties

⊆-isDecPartialOrder : IsDecPartialOrder _≡_ _⊆_
⊆-isDecPartialOrder = record
  { isPartialOrder = ⊆-isPartialOrder
  ; _≟_            = _≡?_
  ; _≤?_           = _⊆?_
  }

⊆-decPoset : DecPoset a a a
⊆-decPoset = record
  { isDecPartialOrder = ⊆-isDecPartialOrder
  }

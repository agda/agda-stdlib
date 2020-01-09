------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation with respect to a
-- setoid which is decidable. This is a generalisation of what is
-- commonly known as Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Sublist.DecSetoid
  {c ℓ} (S : DecSetoid c ℓ) where

import Data.List.Relation.Binary.Equality.DecSetoid as DecSetoidEquality
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeterogeneousProperties
open import Level using (_⊔_)

open DecSetoid S
open DecSetoidEquality S

------------------------------------------------------------------------
-- Re-export core definitions

open SetoidSublist setoid public

------------------------------------------------------------------------
-- Additional relational properties

_⊆?_ : Decidable _⊆_
_⊆?_ = HeterogeneousProperties.sublist? _≟_

⊆-isDecPartialOrder : IsDecPartialOrder _≋_ _⊆_
⊆-isDecPartialOrder = record
  { isPartialOrder = ⊆-isPartialOrder
  ; _≟_            = _≋?_
  ; _≤?_           = _⊆?_
  }

⊆-decPoset : DecPoset c (c ⊔ ℓ) (c ⊔ ℓ)
⊆-decPoset = record
  { isDecPartialOrder = ⊆-isDecPartialOrder
  }

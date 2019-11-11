------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Heterogeneous`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Heterogeneous.Definitions where

open import Level
import Relation.Binary.Core as B
import Relation.Binary.Definitions as B
import Relation.Binary.PropositionalEquality.Core as P
open import Relation.Binary.Indexed.Heterogeneous.Core

private
  variable
    i a ℓ : Level
    I : Set i

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

Reflexive : (A : I → Set a) → IRel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

Symmetric : (A : I → Set a) → IRel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i j} → B.Sym (_∼_ {i} {j}) _∼_

Transitive : (A : I → Set a) → IRel A ℓ → Set _
Transitive _ _∼_ = ∀ {i j k} → B.Trans _∼_ (_∼_ {j}) (_∼_ {i} {k})

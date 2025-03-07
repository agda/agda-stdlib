------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Heterogeneous`.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Indexed.Heterogeneous.Definitions where

open import Level using (Level)
import Relation.Binary.Definitions as B
  using (Reflexive; Symmetric; Transitive; Sym; Trans)
open import Relation.Binary.Indexed.Heterogeneous.Core using (IRel)

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

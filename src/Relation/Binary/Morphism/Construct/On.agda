------------------------------------------------------------------------
-- The Agda standard library
--
-- Construct Morphisms from a relation and a function via `_on_`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Morphism.Construct.On
  {a b ℓ} {A : Set a} {B : Set b} (_∼_ : Rel B ℓ) (f : A → B)
  where

open import Function.Base using (id; _on_)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

------------------------------------------------------------------------
-- Definition

_≈_ : Rel A _
_≈_ = _∼_ on f

isRelHomomorphism : IsRelHomomorphism _≈_ _∼_ f
isRelHomomorphism = record { cong = id }

isRelMonomorphism : IsRelMonomorphism _≈_ _∼_ f
isRelMonomorphism = record
  { isHomomorphism = isRelHomomorphism
  ; injective = id
  }

module ι = IsRelMonomorphism isRelMonomorphism


------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a partial setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Partial

module Relation.Binary.Reasoning.PartialSetoid {s₁ s₂} {A : Set s₁} (S : PartialSetoid A s₂) where

open PartialSetoid S

------------------------------------------------------------------------
-- Publicly re-export base contents

open import Relation.Binary.Reasoning.Base.Partial _≈_ trans public
  renaming (_∼⟨_⟩_ to _≈⟨_⟩_)

infixr 2 _≈˘⟨_⟩_

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ x≈y ⟩ y∼z = x ≈⟨ sym x≈y ⟩ y∼z

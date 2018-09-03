------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding an Infimum to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Free.Infimum {k} (Key : Set k) where

open import Agda.Builtin.Equality

data Key⁺ : Set k where
  ⊥⁺  : Key⁺
  [_] : Key → Key⁺

[_]-injective : ∀ {k l} → [ k ] ≡ [ l ] → k ≡ l
[_]-injective refl = refl

------------------------------------------------------------------------
-- The Agda standard library
--
-- Keys for AVL trees
-- The key type extended with a new minimum and maximum.
------------------------------------------------------------------------

module Data.AVL.Key {k} (Key : Set k) where

open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)

infix 5 [_]

data Key⁺ : Set k where
  ⊥⁺ ⊤⁺ : Key⁺
  [_]   : (k : Key) → Key⁺

[_]-injective : ∀ {k l} → [ k ] ≡ [ l ] → k ≡ l
[_]-injective refl = refl

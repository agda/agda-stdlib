------------------------------------------------------------------------
-- The Agda standard library
--
-- A number of relations defined over compatible equivalence over List of
-- some type, up to reflexivity of the subset relation.
------------------------------------------------------------------------

module Data.List.Sets.Propositional.Structures {a} {A : Set a} where

open import Relation.Binary
open import Data.List.Base
open import Data.List.Sets.Propositional

import Data.List.Sets.Setoid.Structures as SetoidStructures

module ⊆-Structs {ℓ′}
    {_≋_     : Rel (List A) ℓ′}
    (≋-equiv : IsEquivalence _≋_)
    (⊆-reflexive : _≋_ ⇒ _⊆_) = SetoidStructures.⊆-Structs (setoid A)

module ⊆′-Structs {ℓ′}
    {_≋_     : Rel (List A) ℓ′}
    (≋-equiv : IsEquivalence _≋_)
    (⊆′-reflexive : _≋_ ⇒ _⊆_) = SetoidStructures.⊆′-Structs (setoid A)

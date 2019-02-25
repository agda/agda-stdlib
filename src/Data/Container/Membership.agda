------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership for containers
------------------------------------------------------------------------

module Data.Container.Membership where

open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

open import Data.Container.Core
open import Data.Container.Relation.Unary.Any

module _ {s p} {C : Container s p} {x} {X : Set x} where

  infix 4 _∈_
  _∈_ : X → Pred (⟦ C ⟧ X) (p ⊔ x)
  x ∈ xs = ◇ C (_≡_ x) xs

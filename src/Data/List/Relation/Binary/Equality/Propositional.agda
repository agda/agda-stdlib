------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality over lists using propositional equality
------------------------------------------------------------------------

-- Note think carefully about using this module as pointwise
-- propositional equality can usually be replaced with propositional
-- equality.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Equality.Propositional {a} {A : Set a} where

open import Data.List
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Re-export everything from setoid equality

open SetoidEquality (P.setoid A) public

------------------------------------------------------------------------
-- ≋ is propositional

≋⇒≡ : _≋_ ⇒ _≡_
≋⇒≡ []               = P.refl
≋⇒≡ (P.refl ∷ xs≈ys) = P.cong (_ ∷_) (≋⇒≡ xs≈ys)

≡⇒≋ : _≡_ ⇒ _≋_
≡⇒≋ P.refl = ≋-refl

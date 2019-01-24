------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality over lists using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Equality.Propositional {a} {A : Set a} where

open import Data.List
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Publically re-export everything from setoid equality

open SetoidEquality (setoid A) public

------------------------------------------------------------------------
-- ≋ is propositional

≋⇒≡ : _≋_ ⇒ _≡_
≋⇒≡ []             = refl
≋⇒≡ (refl ∷ xs≈ys) = cong (_ ∷_) (≋⇒≡ xs≈ys)

≡⇒≋ : _≡_ ⇒ _≋_
≡⇒≋ refl = ≋-refl

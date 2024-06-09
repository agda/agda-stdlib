------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality over lists using propositional equality
------------------------------------------------------------------------

-- Note think carefully about using this module as pointwise
-- propositional equality can usually be replaced with propositional
-- equality.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (_⇒_)

module Data.List.Relation.Binary.Equality.Propositional {a} {A : Set a} where

open import Data.List.Base
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡

------------------------------------------------------------------------
-- Re-export everything from setoid equality

open SetoidEquality (≡.setoid A) public

------------------------------------------------------------------------
-- ≋ is propositional

≋⇒≡ : _≋_ ⇒ _≡_
≋⇒≡ []             = refl
≋⇒≡ (refl ∷ xs≈ys) = cong (_ ∷_) (≋⇒≡ xs≈ys)

≡⇒≋ : _≡_ ⇒ _≋_
≡⇒≋ refl = ≋-refl

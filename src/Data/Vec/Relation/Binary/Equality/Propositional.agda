------------------------------------------------------------------------
-- The Agda standard library
--
-- Vector equality over propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.Vec.Relation.Binary.Equality.Propositional {a} {A : Set a} where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
import Data.Vec.Relation.Binary.Equality.Setoid as SEq
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Publically re-export everything from setoid equality

open SEq (setoid A) public

------------------------------------------------------------------------
-- ≋ is propositional

≋⇒≡ : ∀ {n} {xs ys : Vec A n} → xs ≋ ys → xs ≡ ys
≋⇒≡ = Pointwise-≡⇒≡

≡⇒≋ : ∀ {n} {xs ys : Vec A n} → xs ≡ ys → xs ≋ ys
≡⇒≋ = ≡⇒Pointwise-≡

-- See also Data.Vec.Relation.Binary.Equality.Propositional.WithK.≋⇒≅.

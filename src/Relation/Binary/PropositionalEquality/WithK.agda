------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to propositional equality that relies on the K
-- rule
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Relation.Binary.PropositionalEquality.WithK where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Proof irrelevance

≡-irrelevance : ∀ {a} {A : Set a} → Irrelevant (_≡_ {A = A})
≡-irrelevance refl refl = refl

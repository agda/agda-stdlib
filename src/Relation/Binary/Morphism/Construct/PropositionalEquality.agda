------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional Equality Lemmas over Morphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

module Relation.Binary.Morphism.Construct.PropositionalEquality where

cong-IsRelHomomorphism : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → IsRelHomomorphism _≡_ _≡_ f
cong-IsRelHomomorphism f .IsRelHomomorphism.cong = cong f

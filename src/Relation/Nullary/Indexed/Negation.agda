------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of indexed negation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Indexed.Negation where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Empty.Polymorphic
open import Function
open import Function.Properties
import Function.Construct.Identity as Identity
open import Relation.Nullary.Indexed

------------------------------------------------------------------------
-- ¬_ preserves ↔ (assuming extensionality)

¬-cong : ∀ {a b c} {A : Set a} {B : Set b} →
         Extensionality a c → Extensionality b c →
         A ↔ B → (¬ c A) ↔ (¬ c B)
¬-cong extA extB A≈B = →-cong-↔ extA extB A≈B (Identity.id-↔ ⊥)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of indexed negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Indexed.Negation where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Function.Bundles using (_↔_)
open import Function.Properties using (→-cong-↔)
import Function.Construct.Identity as Identity using (↔-id)
open import Relation.Nullary.Indexed

------------------------------------------------------------------------
-- ¬_ preserves ↔ (assuming extensionality)

¬-cong : ∀ {a b c} {A : Set a} {B : Set b} →
         Extensionality a c → Extensionality b c →
         A ↔ B → (¬ c A) ↔ (¬ c B)
¬-cong extA extB A≈B = →-cong-↔ extA extB A≈B (Identity.↔-id ⊥)

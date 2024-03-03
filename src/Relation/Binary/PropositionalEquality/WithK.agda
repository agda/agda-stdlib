------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to propositional equality that relies on the K
-- rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.PropositionalEquality.WithK where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Relation.Binary.Definitions using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Core

------------------------------------------------------------------------
-- Re-exporting safe erasure function

-- ≡-erase ignores its `x ≡ y` argument and reduces to refl whenever
-- x and y are judgmentally equal. This is useful when the computation
-- producing the proof `x ≡ y` is expensive.

open import Agda.Builtin.Equality.Erase
  using ()
  renaming ( primEraseEquality to ≡-erase )
  public

------------------------------------------------------------------------
-- Proof irrelevance

≡-irrelevant : ∀ {a} {A : Set a} → Irrelevant {A = A} _≡_
≡-irrelevant = uip

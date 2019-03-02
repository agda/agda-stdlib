------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to propositional equality that relies on the K
-- rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.PropositionalEquality.WithK where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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

≡-irrelevant : ∀ {a} {A : Set a} → Irrelevant (_≡_ {A = A})
≡-irrelevant refl refl = refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.18

≡-irrelevance = ≡-irrelevant
{-# WARNING_ON_USAGE ≡-irrelevance
"Warning: ≡-irrelevance was deprecated in v0.18.
Please use ≡-irrelevant instead."
#-}

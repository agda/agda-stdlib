------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning uniqueness of identity proofs, with axiom K
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Axiom.UniquenessOfIdentityProofs.WithK where

open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Relation.Binary.PropositionalEquality.Core using (refl)

-- Axiom K implies UIP.

uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl

------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning uniqueness of identity proofs, with axiom K
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Axiom.UIP.WithK where

open import Axiom.UIP
open import Relation.Binary.PropositionalEquality.Core

-- Axiom K implies UIP.

uip : ∀ {a A} → UIP {a} A
uip refl refl = refl

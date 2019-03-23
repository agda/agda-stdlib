------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning uniqueness of identity proofs, with K axiom
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Axiom.UIP.WithK where

open import Axiom.UIP
open import Relation.Binary.PropositionalEquality.Core

-- K implies UIP.

uip : ∀ {a A} → UIP {a} A
uip refl refl = refl

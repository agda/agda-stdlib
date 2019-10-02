------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Sum where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Sum
open import Data.Empty
open import Level
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _⊎_.

infixr 1 _¬-⊎_ _⊎-dec_

_¬-⊎_ : ¬ P → ¬ Q → ¬ (P ⊎ Q)
(¬p ¬-⊎ ¬q) (inj₁ p) = ¬p p
(¬p ¬-⊎ ¬q) (inj₂ q) = ¬q q

_⊎-dec_ : Dec P → Dec Q → Dec (P ⊎ Q)
isYes (p? ⊎-dec q?) = isYes p? ∨ isYes q?
reflects (yes p ⊎-dec q?) = true (inj₁ p)
reflects (no ¬p ⊎-dec yes q) = true (inj₂ q)
reflects (no ¬p ⊎-dec no ¬q) = false [ ¬p , ¬q ]

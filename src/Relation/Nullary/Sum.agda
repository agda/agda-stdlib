------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Sum where

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
yes p ⊎-dec _     = yes (inj₁ p)
_     ⊎-dec yes q = yes (inj₂ q)
no ¬p ⊎-dec no ¬q = no helper
  where
  helper : _ ⊎ _ → ⊥
  helper (inj₁ p) = ¬p p
  helper (inj₂ q) = ¬q q

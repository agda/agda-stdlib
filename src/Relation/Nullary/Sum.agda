------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Sum where

open import Data.Bool.Base
open import Data.Sum.Base
open import Data.Empty
open import Level
open import Relation.Nullary.Reflects
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _⊎_.

infixr 1 _¬-⊎_ _⊎-reflects_ _⊎-dec_

_¬-⊎_ : ¬ P → ¬ Q → ¬ (P ⊎ Q)
_¬-⊎_ = [_,_]

_⊎-reflects_ : ∀ {bp bq} → Reflects P bp → Reflects Q bq →
                           Reflects (P ⊎ Q) (bp ∨ bq)
ofʸ  p ⊎-reflects      _ = ofʸ (inj₁ p)
ofⁿ ¬p ⊎-reflects ofʸ  q = ofʸ (inj₂ q)
ofⁿ ¬p ⊎-reflects ofⁿ ¬q = ofⁿ (¬p ¬-⊎ ¬q)

_⊎-dec_ : Dec P → Dec Q → Dec (P ⊎ Q)
does  (p? ⊎-dec q?) = does p? ∨ does q?
proof (p? ⊎-dec q?) = proof p? ⊎-reflects proof q?

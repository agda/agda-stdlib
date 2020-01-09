------------------------------------------------------------------------
-- The Agda standard library
--
-- Implications of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Implication where

open import Data.Empty
open import Relation.Nullary
open import Level

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _→_.

infixr 2 _→-dec_

_→-dec_ : Dec P → Dec Q → Dec (P → Q)
yes p →-dec no ¬q = no  (λ f → ¬q (f p))
yes p →-dec yes q = yes (λ _ → q)
no ¬p →-dec _     = yes (λ p → ⊥-elim (¬p p))

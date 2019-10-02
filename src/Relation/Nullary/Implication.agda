------------------------------------------------------------------------
-- The Agda standard library
--
-- Implications of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Implication where

open import Data.Bool.Base
open import Data.Empty
open import Function using (_∘_; _$_)
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
isYes (p? →-dec q?) = not (isYes p?) ∨ isYes q?
reflects (yes p →-dec yes q) = true (λ _ → q)
reflects (yes p →-dec no ¬q) = false (¬q ∘ (_$ p))
reflects (no ¬p →-dec q?) = true (⊥-elim ∘ ¬p)

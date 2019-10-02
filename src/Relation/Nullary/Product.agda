------------------------------------------------------------------------
-- The Agda standard library
--
-- Products of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Product where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Product
open import Function
open import Level
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _×_.

infixr 2 _×-dec_

_×-dec_ : Dec P → Dec Q → Dec (P × Q)
isYes (p? ×-dec q?) = isYes p? ∧ isYes q?
reflects (yes p ×-dec yes q) = true (p , q)
reflects (yes p ×-dec no ¬q) = false (¬q ∘ proj₂)
reflects (no ¬p ×-dec q?) = false (¬p ∘ proj₁)

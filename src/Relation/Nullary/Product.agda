------------------------------------------------------------------------
-- The Agda standard library
--
-- Products of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Product where

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
yes p ×-dec yes q = yes (p , q)
no ¬p ×-dec _     = no (¬p ∘ proj₁)
_     ×-dec no ¬q = no (¬q ∘ proj₂)

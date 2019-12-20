------------------------------------------------------------------------
-- The Agda standard library
--
-- Products of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Product where

open import Data.Bool.Base
open import Data.Product
open import Function
open import Level
open import Relation.Nullary.Reflects
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _×_.

infixr 2 _×-reflects_ _×-dec_

_×-reflects_ : ∀ {bp bq} → Reflects P bp → Reflects Q bq →
                           Reflects (P × Q) (bp ∧ bq)
ofʸ  p ×-reflects ofʸ  q = ofʸ (p , q)
ofʸ  p ×-reflects ofⁿ ¬q = ofⁿ (¬q ∘ proj₂)
ofⁿ ¬p ×-reflects _      = ofⁿ (¬p ∘ proj₁)

_×-dec_ : Dec P → Dec Q → Dec (P × Q)
does  (p? ×-dec q?) = does p? ∧ does q?
proof (p? ×-dec q?) = proof p? ×-reflects proof q?

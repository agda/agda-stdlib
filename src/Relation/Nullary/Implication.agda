------------------------------------------------------------------------
-- The Agda standard library
--
-- Implications of nullary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Implication where

open import Data.Bool.Base
open import Data.Empty
open import Function.Base
open import Relation.Nullary
open import Level

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Some properties which are preserved by _→_.

infixr 2 _→-reflects_ _→-dec_

_→-reflects_ : ∀ {bp bq} → Reflects P bp → Reflects Q bq →
                           Reflects (P → Q) (not bp ∨ bq)
ofʸ  p →-reflects ofʸ  q = ofʸ (const q)
ofʸ  p →-reflects ofⁿ ¬q = ofⁿ (¬q ∘ (_$ p))
ofⁿ ¬p →-reflects _      = ofʸ (⊥-elim ∘ ¬p)

_→-dec_ : Dec P → Dec Q → Dec (P → Q)
does  (p? →-dec q?) = not (does p?) ∨ does q?
proof (p? →-dec q?) = proof p? →-reflects proof q?

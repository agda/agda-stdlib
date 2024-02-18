--------------------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybes where all the elements satisfy a given property and nothing another property
--------------------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Relation.Unary.AllBoth where

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Level
open import Relation.Unary

------------------------------------------------------------------------
-- Definition

data AllBoth {a p q} {A : Set a} (P : Pred A p) (Q : Set q) : Pred (Maybe A) (a ⊔ p ⊔ q) where
  just    : ∀ {x} → P x → AllBoth P Q (just x)
  nothing : Q → AllBoth P Q nothing

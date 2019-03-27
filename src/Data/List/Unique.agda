------------------------------------------------------------------------
-- The Agda standard library
--
-- Unique Lists
-- Lists which contain no duplicate elements.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Unique where

open import Level using (Level; suc)
open import Data.List
open import Data.List.Membership.Propositional

data Unique {c : Level} {A : Set c} : List A → Set (suc c) where
  nil  : Unique []
  cons : ∀ {x xs} → x ∉ xs → Unique xs → Unique (x ∷ xs)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number types and operations requiring the axiom K.
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Nat.WithK where

open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.WithK

≤″-erase : ∀ {m n} → m ≤″ n → m ≤″ n
≤″-erase (less-than-or-equal eq) = less-than-or-equal (≡-erase eq)

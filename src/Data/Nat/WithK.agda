------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number types and operations requiring the axiom K.
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Nat.WithK where

open import Algebra.Definitions.RawMagma using (_,_)
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.WithK

≤″-erase : ∀ {m n} → m ≤″ n → m ≤″ n
≤″-erase (_ , eq) = _ , ≡-erase eq

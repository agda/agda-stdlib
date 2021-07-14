------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe operations over linear congruential pseudo random generators
-- for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Codata.Stream using (Stream; unfold)
open import Data.Nat.PseudoRandom.LCG
open import Data.Nat using (ℕ)
open import Data.Product using (<_,_>)
open import Function.Base using (id)

module Data.Nat.PseudoRandom.LCG.Unsafe where

------------------------------------------------------------------------
-- An infinite stream of random numbers

stream : Generator → ℕ → Stream ℕ _
stream gen = unfold < step gen , id >

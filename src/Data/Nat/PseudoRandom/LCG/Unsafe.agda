------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe operations over linear congruential pseudo random generators
-- for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

open import Codata.Sized.Stream using (Stream; iterate)
open import Data.Nat.PseudoRandom.LCG using (Generator; step)
open import Data.Nat.Base using (ℕ)
open import Function.Base using (_∘_)

module Data.Nat.PseudoRandom.LCG.Unsafe where

------------------------------------------------------------------------
-- An infinite stream of random numbers

stream : Generator → ℕ → Stream ℕ _
stream = iterate ∘ step

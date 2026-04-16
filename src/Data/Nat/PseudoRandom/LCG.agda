------------------------------------------------------------------------
-- The Agda standard library
--
-- Linear congruential pseudo random generators for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.PseudoRandom.LCG where

open import Data.Nat.Base using (ℕ; _+_; _*_; _^_; NonZero)
open import Data.Nat.DivMod using (_%_)
open import Data.List.Base using (List; iterate)

------------------------------------------------------------------------
-- Type and generator

record Generator : Set where
  field multiplier     : ℕ
        increment      : ℕ
        modulus        : ℕ
        .{{modulus≢0}} : NonZero modulus

  step : ℕ → ℕ
  step x = (multiplier * x + increment) % modulus

open Generator public using (step)

list : ℕ → Generator → ℕ → List ℕ
list k gen x = iterate (step gen) x k

------------------------------------------------------------------------
-- Examples of parameters
-- Taken from https://en.wikipedia.org/wiki/Linear_congruential_generator

-- /!\ As explained in that wikipedia entry, none of these are claimed
-- to be good parameters.

-- Note also that if you need your output to have good properties you
-- may need to postprocess the stream of values to only use some of the
-- bits of the output!

glibc : Generator
glibc = record
  { multiplier = 1103515245
  ; increment  = 12345
  ; modulus    = 2 ^ 31
  }

random0 : Generator
random0 = record
  { multiplier = 8121
  ; increment  = 28411
  ; modulus    = 134456
  }

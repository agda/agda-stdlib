------------------------------------------------------------------------
-- The Agda standard library
--
-- Linear congruential pseudo random generators for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.PseudoRandom.LCG where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≟_)
open import Data.Nat.DivMod using (_%_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Nullary.Decidable using (False)

------------------------------------------------------------------------
-- Type and generator

record Generator : Set where
  field multiplier  : ℕ
        increment   : ℕ
        modulus     : ℕ
        {modulus≢0} : False (modulus ≟ 0)

step : Generator → ℕ → ℕ
step gen x =
  let open Generator gen in
  ((multiplier * x + increment) % modulus) {modulus≢0}

list : ℕ → Generator → ℕ → List ℕ
list zero    gen x = []
list (suc k) gen x = x ∷ list k gen (step gen x)

------------------------------------------------------------------------
-- Examples of parameters
-- Taken from https://en.wikipedia.org/wiki/Linear_congruential_generator

-- /!\ As explained in that wikipedia entry, none of these are claimed to
-- be good parameters.

-- Note also that if you need your output to have good properties you may
-- need to postprocess the stream of values to only use some of the bits of
-- the output!

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

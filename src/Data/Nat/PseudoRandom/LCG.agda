------------------------------------------------------------------------
-- The Agda standard library
--
-- Linear congruential pseudo random generators for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Data.Nat.PseudoRandom.LCG where

open import Codata.Stream using (Stream; unfold)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≟_)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (<_,_>)
open import Function.Base using (id)
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

stream : Generator → ℕ → Stream ℕ _
stream gen = unfold < step gen , id >

------------------------------------------------------------------------
-- Examples of parameters
-- Taken from https://en.wikipedia.org/wiki/Linear_congruential_generator

-- /!\ As explained in that wikipedia entry, none of this are claimed to
-- be good. Note also that if you need your output to have good properties
-- you may need to postprocess the stream of values to only use some of the
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

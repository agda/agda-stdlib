------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic of binary represented natural numbers. Initial part.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Base where

open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat.Base as ℕ using (ℕ)

------------------------------------------------------------------------
-- Definition

data Bin : Set where
  0#    : Bin
  2suc  : Bin → Bin    -- n → 2*(1+n)  arbitrary nonzero even
  suc2* : Bin → Bin    -- n → 1 + 2*n  arbitrary odd

------------------------------------------------------------------------
-- Basic operations

double : Bin → Bin
double 0#        = 0#
double (2suc x)  = 2suc (suc2* x)
double (suc2* x) = 2suc (double x)  -- 2(1+x) + 2(1+x) = 2(1+x + 1+x) = 2(1 + 1+2x)

suc : Bin → Bin
suc 0#        =  suc2* 0#
suc (2suc x)  =  suc2* (suc x)   -- 1 + 2(1+x)
suc (suc2* x) =  2suc x          -- 1 + 1 + 2x =  2*(1+x)

pred : Bin → Bin
pred 0#        = 0#
pred (2suc x)  = suc2* x     -- 2(1+x) - 1 =  1+2x
pred (suc2* x) = double x    -- 1 + 2x -1  =  2x

------------------------------------------------------------------------
-- Addition, multiplication and certain related functions

infixl 6 _+_
infixl 7 _*_

_+_ : Op₂ Bin
0#        + y         =  y
x         + 0#        =  x
(2suc x)  + (2suc y)  =  2suc (suc (x + y))
(2suc x)  + (suc2* y) =  suc (2suc (x + y))
(suc2* x) + (2suc y)  =  suc (2suc (x + y))
(suc2* x) + (suc2* y) =  suc (suc2* (x + y))

_*_ : Op₂ Bin
0#        * _         =  0#
_         * 0#        =  0#
(2suc x)  * (2suc y)  =  double (2suc (x + (y + x * y)))
(2suc x)  * (suc2* y) =  2suc (x + y * (2suc x))
(suc2* x) * (2suc y)  =  2suc (y + x * (2suc y))
(suc2* x) * (suc2* y) =  suc2* (x + y * (suc2* x))

------------------------------------------------------------------------
-- Conversion between Bin and ℕ

toℕ : Bin → ℕ
toℕ 0#        =  0
toℕ (2suc x)  =  2 ℕ.* (ℕ.suc (toℕ x))
toℕ (suc2* x) =  ℕ.suc (2 ℕ.* (toℕ x))

-- Costs O(n), could be improved using `_/_` and `_%_`
fromℕ : ℕ → Bin
fromℕ 0          = 0#
fromℕ (ℕ.suc n) = suc (fromℕ n)

------------------------------------------------------------------------
-- Other functions

-- Useful in some termination proofs.
size : Bin → ℕ
size 0#        = 0
size (2suc x)  = ℕ.suc (size x)
size (suc2* x) = ℕ.suc (size x)

------------------------------------------------------------------------
-- Constants

1B = suc 0#
2B = suc 1B
3B = suc 2B
4B = suc 3B
5B = suc 4B
6B = suc 5B
7B = suc 6B
8B = suc 7B
9B = suc 8B

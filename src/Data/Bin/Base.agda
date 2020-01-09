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
  zero   : Bin
  2[1+_] : Bin → Bin    -- n → 2*(1+n)  arbitrary nonzero even
  1+[2_] : Bin → Bin    -- n → 1 + 2*n  arbitrary odd

------------------------------------------------------------------------
-- Basic operations

double : Bin → Bin
double zero     = zero
double 2[1+ x ] = 2[1+ 1+[2 x ] ]
double 1+[2 x ] = 2[1+ (double x) ]

suc : Bin → Bin
suc zero     =  1+[2 zero ]
suc 2[1+ x ] =  1+[2 (suc x) ]
suc 1+[2 x ] =  2[1+ x ]

pred : Bin → Bin
pred zero     = zero
pred 2[1+ x ] = 1+[2 x ]
pred 1+[2 x ] = double x

------------------------------------------------------------------------
-- Addition, multiplication and certain related functions

infixl 6 _+_
infixl 7 _*_

_+_ : Op₂ Bin
zero     + y        =  y
x        + zero     =  x
2[1+ x ] + 2[1+ y ] =  2[1+ (suc (x + y)) ]
2[1+ x ] + 1+[2 y ] =  suc 2[1+ (x + y) ]
1+[2 x ] + 2[1+ y ] =  suc 2[1+ (x + y) ]
1+[2 x ] + 1+[2 y ] =  suc 1+[2 (x + y) ]

_*_ : Op₂ Bin
zero     * _        =  zero
_        * zero     =  zero
2[1+ x ] * 2[1+ y ] =  double 2[1+ (x + (y + x * y)) ]
2[1+ x ] * 1+[2 y ] =  2[1+ (x + y * 2[1+ x ]) ]
1+[2 x ] * 2[1+ y ] =  2[1+ (y + x * 2[1+ y ]) ]
1+[2 x ] * 1+[2 y ] =  1+[2 (x + y * 1+[2 x ]) ]

------------------------------------------------------------------------
-- Conversion between Bin and ℕ

toℕ : Bin → ℕ
toℕ zero     =  0
toℕ 2[1+ x ] =  2 ℕ.* (ℕ.suc (toℕ x))
toℕ 1+[2 x ] =  ℕ.suc (2 ℕ.* (toℕ x))

-- Costs O(n), could be improved using `_/_` and `_%_`
fromℕ : ℕ → Bin
fromℕ 0         = zero
fromℕ (ℕ.suc n) = suc (fromℕ n)

------------------------------------------------------------------------
-- Other functions

-- Useful in some termination proofs.
size : Bin → ℕ
size zero     = 0
size 2[1+ x ] = ℕ.suc (size x)
size 1+[2 x ] = ℕ.suc (size x)

------------------------------------------------------------------------
-- Constants

0B = zero
1B = suc 0B
2B = suc 1B
3B = suc 2B
4B = suc 3B
5B = suc 4B
6B = suc 5B
7B = suc 6B
8B = suc 7B
9B = suc 8B

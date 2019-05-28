------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic of binary represented natural numbers. Initial part.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Base where

open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat        using (ℕ) renaming (suc to 1+_; _*_ to _*ₙ_)
open import Function        using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary                      using (yes; no)


data Bin : Set
  where
  0#    : Bin
  2suc  : Bin → Bin    -- \n→ 2*(1+n)  arbitrary nonzero even
  suc2* : Bin → Bin    -- \n→ 1 + 2n   arbitrary odd
--
-- This representation is unique for each natural number.


size : Bin → ℕ       -- (number of constructors) - 1.
                       -- It is used in some termination proofs.
size 0#        = 0
size (2suc x)  = 1+ (size x)
size (suc2* x) = 1+ (size x)


------------------------------------------------------------------------------
-- Arithmetic operations on Bin.
------------------------------------------------------------------------------

suc : Bin → Bin
suc 0#        =  suc2* 0#
suc (2suc x)  =  suc2* (suc x)   -- 1 + 2(1+x)
suc (suc2* x) =  2suc x          -- 1 + 1 + 2x =  2*(1+x)


------------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------------

1B = suc 0#
2B = suc 1B
3B = suc 2B
4B = suc 3B
5B = suc 4B
6B = suc 5B
7B = suc 6B
8B = suc 7B
9B = suc 8B


------------------------------------------------------------------------------
-- Addition, multiplication and certain related functions
------------------------------------------------------------------------------

infixl 6 _+_

_+_ : Op₂ Bin
0#        + y         =  y
x         + 0#        =  x
(2suc x)  + (2suc y)  =  2suc (suc (x + y))
                                       -- 2(1+x) + 2(1+y) =  2(1 + 1+x+y)
(2suc x)  + (suc2* y) =  suc (2suc (x + y))
                                       -- 2(1+x) + 1 + 2y =  1 + 2(1+x+y)
(suc2* x) + (2suc y)  =  suc (2suc (x + y))
(suc2* x) + (suc2* y) =  suc (suc2* (x + y))
                              -- 1+2x + 1+2y =  2 + 2(x+y) =  1 + 1 + 2(x+y)

2* : Bin → Bin
2* 0#        = 0#
2* (2suc x)  = 2suc (suc2* x)
                            -- 2(1+x) + 2(1+x) = 2(1+x + 1+x) =  2(1 + 1+2x)
2* (suc2* x) = 2suc (2* x)

pred : Bin → Bin
pred 0#        =  0#
pred (2suc x)  =  suc2* x   -- 2(1+x) - 1 =  1+2x
pred (suc2* x) =  2* x      -- 1 + 2x -1  =  2x

2^ :  ℕ → Bin             -- a power of two
2^ 0      =  1B
2^ (1+ n) =  2* (2^ n)


infixl 7 _*_

_*_ : Op₂ Bin

0#        * _         =  0#
_         * 0#        =  0#
(2suc x)  * (2suc y)  =  2* (2suc (x + (y + x * y)))
(2suc x)  * (suc2* y) =  2suc (x + y * (2suc x))
                      --
                      -- 2(1+x) * (1+2y) =  2(1 + 2y + x + 2xy)
                      --                 =  2(1 + x + y*2(1 + x))

(suc2* x) * (2suc y)  =  2suc (y + x * (2suc y))
(suc2* x) * (suc2* y) =  suc2* (x + y * (suc2* x))
            --
            -- (1 + 2x)(1 + 2y) =  1 + (2y + 2x + 4xy)
            --                     1 + 2(x + y * (1 + 2x))

toℕ : Bin → ℕ
toℕ 0#        =  0
toℕ (2suc x)  =  2 *ₙ (1+ (toℕ x))
toℕ (suc2* x) =  1+ (2 *ₙ (toℕ x))

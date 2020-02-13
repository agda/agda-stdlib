------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers represented in binary.
------------------------------------------------------------------------

-- This module aims to create an alternative formulation of ℕ that is
-- still reasonably computationally efficient without having to call out
-- to Haskell.

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.Base where

open import Algebra.Core using (Op₂)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Sum.Base using (_⊎_)
open import Function using (_on_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Definition

data ℕᵇ : Set where
  zero   : ℕᵇ
  2[1+_] : ℕᵇ → ℕᵇ    -- n → 2*(1+n) = nonzero even numbers
  1+[2_] : ℕᵇ → ℕᵇ    -- n → 1 + 2*n = odd numbers

------------------------------------------------------------------------
-- Ordering relations

infix 4 _<_ _>_ _≤_ _≮_ _≯_ _≰_ _≱_

data _<_ : Rel ℕᵇ 0ℓ  where
  0<even    : ∀ {x} → zero < 2[1+ x ]
  0<odd     : ∀ {x} → zero < 1+[2 x ]
  even<even : ∀ {x y} → x < y → 2[1+ x ] < 2[1+ y ]
  even<odd  : ∀ {x y} → x < y → 2[1+ x ] < 1+[2 y ]
  odd<even  : ∀ {x y} → x < y ⊎ x ≡ y → 1+[2 x ] < 2[1+ y ]
  odd<odd   : ∀ {x y} → x < y → 1+[2 x ] < 1+[2 y ]
  -- In these constructors "even" stands for nonzero even.

_>_ : Rel ℕᵇ 0ℓ
x > y = y < x

_≤_ : Rel ℕᵇ 0ℓ
x ≤ y = x < y ⊎ x ≡ y

_≥_ : Rel ℕᵇ 0ℓ
x ≥ y = y ≤ x

_≮_ : Rel ℕᵇ 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel ℕᵇ 0ℓ
x ≯ y = ¬ (x > y)

_≰_ : Rel ℕᵇ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℕᵇ 0ℓ
x ≱ y = ¬ (x ≥ y)

------------------------------------------------------------------------
-- Basic operations

double : ℕᵇ → ℕᵇ
double zero     = zero
double 2[1+ x ] = 2[1+ 1+[2 x ] ]
double 1+[2 x ] = 2[1+ (double x) ]

suc : ℕᵇ → ℕᵇ
suc zero     =  1+[2 zero ]
suc 2[1+ x ] =  1+[2 (suc x) ]
suc 1+[2 x ] =  2[1+ x ]

pred : ℕᵇ → ℕᵇ
pred zero     = zero
pred 2[1+ x ] = 1+[2 x ]
pred 1+[2 x ] = double x

------------------------------------------------------------------------
-- Addition, multiplication and certain related functions

infixl 6 _+_
infixl 7 _*_

_+_ : Op₂ ℕᵇ
zero     + y        =  y
x        + zero     =  x
2[1+ x ] + 2[1+ y ] =  2[1+ suc (x + y) ]
2[1+ x ] + 1+[2 y ] =  suc 2[1+ (x + y) ]
1+[2 x ] + 2[1+ y ] =  suc 2[1+ (x + y) ]
1+[2 x ] + 1+[2 y ] =  suc 1+[2 (x + y) ]

_*_ : Op₂ ℕᵇ
zero     * _        =  zero
_        * zero     =  zero
2[1+ x ] * 2[1+ y ] =  double 2[1+ x + (y + x * y) ]
2[1+ x ] * 1+[2 y ] =  2[1+ x + y * 2[1+ x ] ]
1+[2 x ] * 2[1+ y ] =  2[1+ y + x * 2[1+ y ] ]
1+[2 x ] * 1+[2 y ] =  1+[2 x + y * 1+[2 x ] ]

------------------------------------------------------------------------
-- Conversion between ℕᵇ and ℕ

toℕ : ℕᵇ → ℕ
toℕ zero     =  0
toℕ 2[1+ x ] =  2 ℕ.* (ℕ.suc (toℕ x))
toℕ 1+[2 x ] =  ℕ.suc (2 ℕ.* (toℕ x))

-- Costs O(n), could be improved using `_/_` and `_%_`
fromℕ : ℕ → ℕᵇ
fromℕ 0         = zero
fromℕ (ℕ.suc n) = suc (fromℕ n)

-- An alternative ordering lifted from ℕ

infix 4 _<ℕ_

_<ℕ_ :  Rel ℕᵇ 0ℓ
_<ℕ_ =  ℕ._<_ on toℕ

------------------------------------------------------------------------
-- Other functions

-- Useful in some termination proofs.
size : ℕᵇ → ℕ
size zero     = 0
size 2[1+ x ] = ℕ.suc (size x)
size 1+[2 x ] = ℕ.suc (size x)

------------------------------------------------------------------------
-- Constants

0ᵇ = zero
1ᵇ = suc 0ᵇ
2ᵇ = suc 1ᵇ
3ᵇ = suc 2ᵇ
4ᵇ = suc 3ᵇ
5ᵇ = suc 4ᵇ
6ᵇ = suc 5ᵇ
7ᵇ = suc 6ᵇ
8ᵇ = suc 7ᵇ
9ᵇ = suc 8ᵇ

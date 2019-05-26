------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic of binary represented natural numbers. Initial part.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Base where

import      Algebra.FunctionProperties as FuncProp
open import Data.Nat using (ℕ) renaming (suc to 1+_; _*_ to _*ₙ_)
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


open FuncProp (_≡_ {A = Bin}) using (Op₂)

2suc-injective : {x y : Bin} → 2suc x ≡ 2suc y → x ≡ y
2suc-injective {0#}      {0#}      _    =  refl
2suc-injective {2suc _}  {2suc _}  refl =  refl
2suc-injective {suc2* _} {suc2* _} refl =  refl

suc2*-injective : {x y : Bin} → suc2* x ≡ suc2* y → x ≡ y
suc2*-injective {0#}      {0#}      _    =  refl
suc2*-injective {2suc _}  {2suc _}  refl =  refl
suc2*-injective {suc2* _} {suc2* _} refl =  refl

-- Decidable equality on Bin.

_≟_ :  Decidable (_≡_ {A = Bin})

0#        ≟ 0#        =  yes refl
0#        ≟ (2suc _)  =  no λ()
0#        ≟ (suc2* _) =  no λ()
(2suc _)  ≟ 0#        =  no λ()
(2suc x)  ≟ (2suc y)  with x ≟ y
... | yes eq =  yes (cong 2suc eq)
... | no ne  =  no (ne ∘ 2suc-injective)

(2suc _)  ≟ (suc2* _) =  no λ()
(suc2* _) ≟ 0#        =  no λ()
(suc2* _) ≟ (2suc _)  =  no λ()
(suc2* x) ≟ (suc2* y) with x ≟ y
... | yes eq =  yes (cong suc2* eq)
... | no ne  =  no (ne ∘ suc2*-injective)

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

1# = suc 0#;   2# = suc 1#;   3# = suc 2#;   4# = suc 3#;   5# = suc 4#


infixl 6 _+_

_+_ : Op₂ Bin                               -- addition
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

2^ :  ℕ → Bin          -- a power of two
2^ 0      =  1#
2^ (1+ n) =  2* (2^ n)


infixl 7 _*_

_*_ : Op₂ Bin                -- multipication

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


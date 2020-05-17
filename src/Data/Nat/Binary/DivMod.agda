------------------------------------------------------------------------
-- The Agda standard library
--
-- Division with remainder on binary represented naturals.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.DivMod where

open import Data.Nat.Binary.Base
open import Data.Nat.Binary.Induction
open import Data.Nat.Binary.Properties
open import Data.Nat.Binary.Subtraction
open import Function using (_∘_)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Binary.PropositionalEquality as P using
  (_≡_; _≢_; refl; sym; cong; cong₂; resp₂)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc)
open Acc using (acc)
open InequalityReasoning {A = ℕᵇ} {_≈_ = _≡_} ≤-isPreorder <-trans (resp₂ _<_)
                         <⇒≤ <-≤-trans ≤-<-trans
open ℕᵇ

------------------------------------------------------------------------------
-- DivMod  is the definition of what is division with remainder,
-- and it is the result type for division with remainder. It includes certain
-- two property witnesses for the quotient and remainder.
--
-- Note that  divisor ≢ 0ᵇ  can be derived from  res : DivMod _ divisor.
------------------------------------------------------------------------------

record DivMod (dividend divisor : ℕᵇ) : Set where  -- result of division with remainder
  constructor divModᶜ
  field
    quotient    : ℕᵇ
    remainder   : ℕᵇ
    equality    : dividend ≡ remainder + quotient * divisor
    rem<divisor : remainder < divisor

------------------------------------------------------------------------------
-- Evaluating division with remainder.
-- Illustration:  divMod 2a b  for b ≢ 0  is found by reducing it to division of
-- a  by  b  as follows.
-- By recursion, let      a = qb + r,    r < b.
-- Then  2a = 2qb + 2r,   r ≤ 2r < 2b,   r < b  < 2b.
-- If  2r < b  then the result is (2q , 2r),
-- otherwise                      (2q+1, 2r - b).
-- In the latter case it is needed to prove  2r - b < b.
-- This is equivalent to  2r < 2b  ~  r < b.

------------------------------------------------------------------------------
-- Below the module  Even  helps the equality proof for  divMod 2[1+ a ] b.
-- The module  Odd  helps the equality proof for  divMod 1+[2 a ] b.

module Even (a b q r : ℕᵇ) (suc-a≡r+qb : suc a ≡ r + q * b)
  where
  2r   = double r;   2q   = double q;  qb   = q * b
  2*qb = double qb;  2q*b = 2q * b;    2r-b = 2r ∸ b

  2[1+a]≡2r+[2q]b : 2[1+ a ] ≡ double r + (double q) * b
  2[1+a]≡2r+[2q]b = begin-equality
    2[1+ a ]               ≡⟨ 2[1+_]-double-suc a ⟩
    double (suc a)         ≡⟨ cong double suc-a≡r+qb ⟩
    double (r + q * b)     ≡⟨ double-distrib-+ r qb ⟩
    double r + double qb   ≡⟨ cong (2r +_) (sym (double-*-assoc q b)) ⟩
    2r + 2q*b              ∎

  eqFor≮ : double r ≮ b → 2[1+ a ] ≡ ((double r) ∸ b) + 1+[2 q ] * b
  eqFor≮ 2r≮b = begin-equality
    2[1+ a ]                   ≡⟨ 2[1+a]≡2r+[2q]b ⟩
    2r + 2q*b                  ≡⟨ cong (_+ 2q*b) (sym ([x∸y]+y≡x b≤2r)) ⟩
    ((2r ∸ b) + b) + 2q*b      ≡⟨ +-assoc 2r-b b _ ⟩
    2r-b + (b + 2q*b)          ≡⟨ cong (2r-b +_) (sym (suc-* 2q b)) ⟩
    2r-b + (suc 2q) * b        ≡⟨ cong ((2r-b +_) ∘ (_* b))
                                       (sym (1+[2_]-suc-double q)) ⟩
    (2r ∸ b) + 1+[2 q ] * b    ∎
    where
    b≤2r = ≮⇒≥ 2r≮b

module Odd (a b q r : ℕᵇ) (a≡r+qb : a ≡ r + q * b)
  where
  2r = double r;  qb = q * b;  2q = double q;  2q*b = 2q * b

  1+[2a]≡1+[2r]+2q*b :  1+[2 a ] ≡ 1+[2 r ] + 2q * b
  1+[2a]≡1+[2r]+2q*b = begin-equality
    1+[2 a ]                 ≡⟨ 1+[2_]-suc-double a ⟩
    suc (double a)           ≡⟨ cong (suc ∘ double) a≡r+qb ⟩
    suc (double (r + qb))    ≡⟨ cong suc (double-distrib-+ r qb) ⟩
    suc (2r + (double qb))   ≡⟨ sym (suc-+ 2r (double qb)) ⟩
    suc 2r + (double qb)     ≡⟨ cong₂ _+_ (sym (1+[2_]-suc-double r))
                                          (sym (double-*-assoc q b)) ⟩
    1+[2 r ] + 2q * b        ∎

  eqFor≮ :  1+[2 r ] ≮ b → 1+[2 a ] ≡ (1+[2 r ] ∸ b) + 1+[2 q ] * b
  eqFor≮ 1+2r≮b = begin-equality
    1+[2 a ]                        ≡⟨ 1+[2a]≡1+[2r]+2q*b ⟩
    1+[2 r ] + 2q*b                 ≡⟨ cong (_+ 2q*b) (sym ([x∸y]+y≡x b≤1+2r)) ⟩
    ((1+[2 r ] ∸ b) + b) + 2q*b     ≡⟨ +-assoc c b 2q*b ⟩
    (1+[2 r ] ∸ b) + (b + 2q*b)     ≡⟨ cong (c +_) (sym (suc-* 2q b)) ⟩
    (1+[2 r ] ∸ b) + (suc 2q) * b   ≡⟨ cong ((c +_) ∘ (_* b)) (sym (1+[2_]-suc-double q)) ⟩
    (1+[2 r ] ∸ b) + 1+[2 q ] * b   ∎
    where
    c = 1+[2 r ] ∸ b;   b≤1+2r = ≮⇒≥ 1+2r≮b

divMod : (a b : ℕᵇ) → b ≢ 0ᵇ → DivMod a b
divMod a b b≢0 =  dm a (<-wellFounded a)
  where
  -- Accessibility  <-acc for _<_ on ℕᵇ  is used to prove termination.
  -- Because for a ≠ 0,  divMod a b  is reduced to  divMod a' b,  where a' < a.
  -- So that this recursion terminates.

  dm : (a : ℕᵇ) → Acc _<_ a → DivMod a b             -- b is fixed in this loop
  dm zero          _        =  divModᶜ 0ᵇ 0ᵇ refl (x≢0⇒x>0 b≢0)
  dm a'@(2[1+ a ]) (acc wf) =  recurseEven (dm (suc a) (wf _ suc-a<2[1+a]))
    where
    -- wf :  ∀ x → x < 2[1+ a ] → DivMod x b

    suc-a<2[1+a] :  suc a < 2[1+ a ]
    suc-a<2[1+a] =  begin-strict
      suc a            ≡⟨ sym (+-identityʳ (suc a)) ⟩
      suc a + 0ᵇ       <⟨ +-monoʳ-< (suc a) (0<suc a) ⟩
      suc a + suc a    ≡⟨ sym (double[x]≡x+x (suc a)) ⟩
      double (suc a)   ≡⟨ sym (2[1+_]-double-suc a) ⟩
      2[1+ a ]         ∎

    recurseEven : DivMod (suc a) b → DivMod a' b
    recurseEven (divModᶜ q r suc-a≡r+qb r<b) =  aux (2r <? b)
      where
      2r = double r

      aux : Dec (2r < b) → DivMod a' b
      aux (yes 2r<b) =  divModᶜ (double q) 2r
                                (Even.2[1+a]≡2r+[2q]b a b q r suc-a≡r+qb) 2r<b
      aux (no  2r≮b) =  divModᶜ 1+[2q] (2r ∸ b)
                                       (Even.eqFor≮ a b q r suc-a≡r+qb 2r≮b) 2r-b<b
        where
        -- Given:  r<b,  2r>b.
        1+[2q] = 1+[2 q ];  b≤2r = ≮⇒≥ 2r≮b;  2r<2b = double-mono-< r<b
        suc[2r-b]≤b = begin
          suc (2r ∸ b)     ≡⟨ suc≗1+ (2r ∸ b) ⟩
          1ᵇ + (2r ∸ b)    ≡⟨ sym (+-∸-assoc 1ᵇ b≤2r) ⟩
          (1ᵇ + 2r) ∸ b    ≡⟨ cong (_∸ b) (sym (suc≗1+ 2r)) ⟩
          (suc 2r) ∸ b     ≤⟨ ∸-monoˡ-≤ b (x<y⇒suc[x]≤y 2r<2b) ⟩
          (double b) ∸ b   ≡⟨ cong (_∸ b) (double[x]≡x+x b) ⟩
          (b + b) ∸ b      ≡⟨ x+y∸y≡x b b ⟩
          b                ∎

        2r-b<b =  suc[x]≤y⇒x<y suc[2r-b]≤b

  dm a'@(1+[2 a ]) (acc wf) =  recurseOdd (dm a (wf _ a<1+[2a]))
    where
    2a       = double a     -- Given:  a = r + qb;  r<b. Then  1+2a = 1+2r + 2qb ...
    a<1+[2a] = x<1+[2x] a

    recurseOdd : DivMod a b → DivMod a' b
    recurseOdd (divModᶜ q r a≡r+qb r<b) =  aux (1+2r <? b)
      where
      2q = double q;  2r = double r;  1+2r = 1+[2 r ]
      a'≡1+2r+2q*b =  Odd.1+[2a]≡1+[2r]+2q*b a b q r a≡r+qb

      aux : Dec (1+2r < b) → DivMod a' b
      aux (yes 1+2r<b) = divModᶜ 2q 1+2r a'≡1+2r+2q*b 1+2r<b
      aux (no  1+2r≮b) = divModᶜ q' r' a'≡r'+q'b r'<b
        where
        1+2q = 1+[2 q ];   q' = 1+2q;   r' = 1+2r ∸ b

        a'≡r'+q'b    =  Odd.eqFor≮ a b q r a≡r+qb 1+2r≮b
        suc[r]+r≤b+r =  +-monoˡ-≤ r (x<y⇒suc[x]≤y r<b)
        r'<b = begin-strict
          1+2r ∸ b          ≡⟨ cong (_∸ b) (1+[2_]-suc-double r) ⟩
          (suc 2r) ∸ b      ≡⟨ cong ((_∸ b) ∘ suc) (double[x]≡x+x r) ⟩
          suc (r + r) ∸ b   ≡⟨ cong (_∸ b) (sym (suc-+ r r)) ⟩
          (suc r + r) ∸ b   ≤⟨ ∸-monoˡ-≤ b suc[r]+r≤b+r ⟩
          (b + r) ∸ b       ≡⟨ [x+y]∸x≡y b r ⟩
          r                 <⟨ r<b ⟩
          b                 ∎

quot : (a b : ℕᵇ) → b ≢ 0ᵇ → ℕᵇ
quot a b = DivMod.quotient ∘ divMod a b

rem : (a b : ℕᵇ) → b ≢ 0ᵇ → ℕᵇ
rem a b = DivMod.remainder ∘ divMod a b

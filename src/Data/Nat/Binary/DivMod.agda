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
open import Relation.Binary using (Tri)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Binary.PropositionalEquality as P using
  (_≡_; _≢_; refl; sym; cong; resp₂)
open import Induction.WellFounded using (Acc)
open Acc using (acc)
open InequalityReasoning {A = ℕᵇ} {_≈_ = _≡_} ≤-isPreorder <-trans (resp₂ _<_)
                         <⇒≤ <-≤-trans ≤-<-trans
open ℕᵇ
open Tri

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
--
-- In the latter case it is needed to prove  2r - b < b.
-- This is equivalent to  2r < 2b  ~  r < b.
------------------------------------------------------------------------------

divMod : (a b : ℕᵇ) → b ≢ 0ᵇ → DivMod a b
divMod a b b≢0 =  dm a (<-wellFounded a)
  where
  -- Accessibility  <-acc for _<_ on ℕᵇ  is used to prove termination.
  -- Because or a ≠ 0,  divMod a b  is reduced to  divMod a' b,  where a' < a.
  -- So that this recursion terminates.

  dm : (a : ℕᵇ) → Acc _<_ a → DivMod a b             -- b is fixed in this loop
  dm zero          _        =  divModᶜ 0ᵇ 0ᵇ refl (x≢0⇒x>0 b≢0)
  dm a'@(2[1+ a ]) (acc wf) =  correct (dm (suc a) (wf _ suc-a<2[1+a]))
    where
    2b = double b;  1+a = suc a
    -- wf :  ∀ x → x < 2[1+ a ] → DivMod x b

    suc-a<2[1+a] :  suc a < 2[1+ a ]
    suc-a<2[1+a] =  begin-strict
      suc a            ≡⟨ sym (+-identityʳ (suc a)) ⟩
      suc a + 0ᵇ       <⟨ +-monoʳ-< (suc a) (0<suc a) ⟩
      suc a + suc a    ≡⟨ sym (double[x]≡x+x (suc a)) ⟩
      double (suc a)   ≡⟨ sym (2[1+_]-double-suc a) ⟩
      2[1+ a ]         ∎

    correct :  DivMod 1+a b → DivMod a' b
    correct (divModᶜ q r 1+a≡r+qb r<b) =  aux (<-cmp 2r b)
      where
      2r   = double r;  2q  = double q;   qb   = q * b
      2r-b = 2r ∸ b;    2qb = double qb;  2q*b = 2q * b

      aux :  Tri (2r < b) (2r ≡ b) (2r > b) → DivMod a' b
      aux (tri< 2r<b _ _) =  divModᶜ 2q 2r a'≡2r+2qb 2r<b
        where
        a'≡2r+2qb = begin-equality
          2[1+ a ]          ≡⟨ 2[1+_]-double-suc a ⟩
          double 1+a        ≡⟨ cong double 1+a≡r+qb ⟩
          double (r + qb)   ≡⟨ double-distrib-+ r qb ⟩
          2r + double qb    ≡⟨ cong (2r +_) (sym (double-*-assoc q b)) ⟩
          2r + (2q * b)     ∎

      aux (tri≈ _ 2r≡b _) =  divModᶜ 1+[2q] 0ᵇ a'≡0+1+[2q]*b (x≢0⇒x>0 b≢0)
        where
        1+[2q]        = 1+[2 q ]
        a'≡0+1+[2q]*b = begin-equality
          2[1+ a ]            ≡⟨ 2[1+_]-double-suc a ⟩
          double 1+a          ≡⟨ cong double 1+a≡r+qb ⟩
          double (r + qb)     ≡⟨ double-distrib-+ r qb ⟩
          2r + (double qb)    ≡⟨ cong (_+ (double qb)) 2r≡b ⟩
          b + (double qb)     ≡⟨ cong (b +_) (sym (double-*-assoc q b)) ⟩
          b + 2q * b          ≡⟨ sym (suc-* 2q b) ⟩
          (suc 2q) * b        ≡⟨ cong (_* b) (sym (1+[2_]-suc-double q)) ⟩
          1+[2 q ] * b        ≡⟨ sym (+-identityˡ (1+[2 q ] * b)) ⟩
          0ᵇ + 1+[2 q ] * b   ∎

      aux (tri> _ _ 2r>b) =  divModᶜ 1+[2q] 2r-b a'≡[2r-b]+1+[2q]*b 2r-b<b
        where
        -- Given:  r<b,  2r>b.

        1+[2q] = 1+[2 q ];  b≤2r = <⇒≤ 2r>b;  2r<2b = double-mono-< r<b
        suc[2r-b]≤b = begin
          suc (2r ∸ b)    ≡⟨ suc≗1+ 2r-b ⟩
          1ᵇ + (2r ∸ b)   ≡⟨ sym (+-∸-assoc 1ᵇ b≤2r) ⟩
          (1ᵇ + 2r) ∸ b   ≡⟨ cong (_∸ b) (sym (suc≗1+ 2r)) ⟩
          (suc 2r) ∸ b    ≤⟨ ∸-monoˡ-≤ b (x<y⇒suc[x]≤y 2r<2b) ⟩
          2b ∸ b          ≡⟨ cong (_∸ b) (double[x]≡x+x b) ⟩
          (b + b) ∸ b     ≡⟨ x+y∸y≡x b b ⟩
          b               ∎

        2r-b<b             =  suc[x]≤y⇒x<y suc[2r-b]≤b
        a'≡[2r-b]+1+[2q]*b =  begin-equality
          2[1+ a ]                  ≡⟨ 2[1+_]-double-suc a ⟩
          double (suc a)            ≡⟨ cong double 1+a≡r+qb ⟩
          double (r + qb)           ≡⟨ double-distrib-+ r qb ⟩
          2r + 2qb                  ≡⟨ cong (2r +_) (sym (double-*-assoc q b)) ⟩
          2r + 2q*b                 ≡⟨ cong (_+ 2q*b) (sym ([x∸y]+y≡x b≤2r)) ⟩
          (2r-b + b) + 2q*b         ≡⟨ +-assoc 2r-b b 2q*b ⟩
          2r-b + (b + 2q*b)         ≡⟨ cong (2r-b +_) (sym (suc-* 2q b)) ⟩
          2r-b + (suc 2q) * b       ≡⟨ cong ((2r-b +_) ∘ (_* b))
                                            (sym (1+[2_]-suc-double q)) ⟩
          (2r ∸ b) + 1+[2 q ] * b   ∎

  dm a'@(1+[2 a ]) (acc wf) =  correct (dm a (wf _ a<1+[2a]))
    where
    2a = double a
    {- Given:  a = r + qb;   r<b.
       1+2a = 1+2r + 2qb
       (q', r') =  if  1+2r<b  then (2q , 1 + 2r)
                   else             -- b≤1+2r
                                    (1+2q , 1 + 2r - b)
    -}
    a<1+[2a] =  x<1+[2x] a

    correct :  DivMod a b → DivMod a' b
    correct (divModᶜ q r a≡r+qb r<b) =  aux (<-cmp suc[2r] b)
      where
      2r = double r;   suc[2r] = suc 2r;      2q   = double q
      qb = q * b;      2*qb    = double qb;   2q*b = 2q * b

      a'≡suc[2r]+2q*b = begin-equality
        1+[2 a ]               ≡⟨ 1+[2_]-suc-double a ⟩
        suc (double a)         ≡⟨ cong (suc ∘ double) a≡r+qb ⟩
        suc (double (r + qb))  ≡⟨ cong suc (double-distrib-+ r qb) ⟩
        suc (2r + 2*qb)        ≡⟨ sym (suc-+ 2r 2*qb) ⟩
        suc[2r] + 2*qb         ≡⟨ cong (suc[2r] +_) (sym (double-*-assoc q b)) ⟩
        suc[2r] + 2q*b         ∎

      aux :  Tri (suc[2r] < b) (suc[2r] ≡ b) (suc[2r] > b) → DivMod a' b
      aux (tri< suc[2r]<b _ _) = divModᶜ 2q suc[2r] a'≡suc[2r]+2q*b suc[2r]<b
      aux (tri≈ _ suc[2r]≡b _) = divModᶜ q' 0ᵇ a'≡0+q'b (x≢0⇒x>0 b≢0)
        where
        q'       = suc 2q
        q'b      = q' * b
        a'≡0+q'b = begin-equality
          a'               ≡⟨ a'≡suc[2r]+2q*b ⟩
          suc[2r] + 2q*b   ≡⟨ cong (_+ 2q*b) suc[2r]≡b ⟩
          b + 2q*b         ≡⟨ sym (suc-* 2q b) ⟩
          q' * b           ≡⟨ sym (+-identityˡ q'b) ⟩
          0ᵇ + q'b         ∎

      aux (tri> _ _ suc[2r]>b) =  divModᶜ q' r' a'≡r'+q'b (begin-strict
        suc[2r] ∸ b        ≡⟨ cong ((_∸ b) ∘ suc) (double[x]≡x+x r) ⟩
        suc (r + r) ∸ b    ≡⟨ cong (_∸ b) (sym (suc-+ r r)) ⟩
        (suc r + r) ∸ b    ≤⟨ ∸-monoˡ-≤ b suc[r]+r≤b+r ⟩
        (b + r) ∸ b        ≡⟨ [x+y]∸x≡y b r ⟩
        r                  <⟨ r<b ⟩
        b                  ∎)
        where
        q' = suc 2q;   r' = suc[2r] ∸ b;    q'b = q' * b

        b≤suc[2r]    =  <⇒≤ suc[2r]>b
        suc[r]+r≤b+r =  +-monoˡ-≤ r (x<y⇒suc[x]≤y r<b)
        a'≡r'+q'b    =  begin-equality
          a'                          ≡⟨ a'≡suc[2r]+2q*b ⟩
          suc[2r] + 2q*b              ≡⟨ cong (_+ 2q*b) (sym ([x∸y]+y≡x b≤suc[2r])) ⟩
          ((suc[2r] ∸ b) + b) + 2q*b  ≡⟨ +-assoc r' b 2q*b ⟩
          r' + (b + 2q*b)             ≡⟨ cong (r' +_) (sym (suc-* 2q b)) ⟩
          r' + (suc 2q) * b           ≡⟨ refl ⟩
          r' + q'b                    ∎

quot : (a b : ℕᵇ) → b ≢ 0ᵇ → ℕᵇ
quot a b = DivMod.quotient ∘ divMod a b

rem : (a b : ℕᵇ) → b ≢ 0ᵇ → ℕᵇ
rem a b = DivMod.remainder ∘ divMod a b

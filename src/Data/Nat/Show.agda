------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Show where

open import Data.Char as Char using (Char)
open import Data.Digit using (showDigit; toDigits)
open import Function   using (_∘_; _$_)
open import Data.List  using (List; []; _∷_; map; reverse)
open import Data.Nat   using (ℕ; _≟_; suc; pred; _+_; _*_; _<_; _>_; z≤n; s≤s;
                                                                      _≤?_)
open import Data.Nat.DivMod     using (_div_; _%_; a≡a%n+[a/n]*n)
open import Data.Product        using (proj₁)
open import Data.Nat.Properties using
            (+-comm; *-identityʳ; <-irrefl; <⇒≢; ≢0⇒>; m≤m+n; *-monoʳ-<;
             m<m*n; m≢0⇒suc[pred[m]]≡m; module ≤-Reasoning
            )
open import Data.String as String using (String)
open import Induction.Nat         using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym;
                                                         cong; ≢-sym)
open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Nullary.Negation  using (contradiction)


------------------------------------------------------------------------------
open ≤-Reasoning

-- Conversion from unary representation to the representation by the given
-- base. 
toDigitNats : (base : ℕ) → base > 1 → ℕ → List ℕ
toDigitNats 0             ()
toDigitNats 1             (s≤s ())
toDigitNats (suc (suc b)) base>1 x =  aux x (<-wellFounded x) [] 
  where
  -- <-wellFounded  means that _<_ is well-founded on ℕ
  --                ("each number in ℕ is accessible from 0 by _<_").

  base = suc (suc b);  pbase = pred base

  aux : (n : ℕ) → Acc _<_ n → List ℕ → List ℕ 
  aux 0       _        =  (0 ∷_)
  aux (suc n) (acc wf) =  aux'
    where
    n' = suc n;   q = n' div base;   r = n' % base;   pq = pred q

    n'≡r+q*base :  n' ≡ r + q * base
    n'≡r+q*base =  a≡a%n+[a/n]*n n' pbase

    aux' : List ℕ → List ℕ
    aux' with q ≟ 0
    ... | yes _   =  (r ∷_)
    ... | no q≢0 =  aux q (wf _ q<n') ∘ (r ∷_)   -- use  n' ≡ r + q*base 
      where
      q>0       = ≢0⇒> q≢0
      suc-pq≡q = m≢0⇒suc[pred[m]]≡m q≢0
      q<q*base  = m<m*n q>0 base>1
      q<n' =
        begin suc q            ≤⟨ q<q*base ⟩
              q * base         ≤⟨ m≤m+n (q * base) r ⟩ 
              q * base + r    ≡⟨ +-comm _ r ⟩
              r + q * base    ≡⟨ sym n'≡r+q*base ⟩
              n'
        ∎

toDigitChar : (n : ℕ) → Char
toDigitChar n =  Char.fromNat (n + 48) 

toDecimalChars : ℕ → List Char
toDecimalChars = map toDigitChar ∘ toDigitNats 10 1<10
  where
  1<10 = s≤s (s≤s z≤n)

show : ℕ → String                 
show = String.fromList ∘ toDecimalChars
--
-- (show n) is a string containing the decimal expansion of n (starting
-- with the most significant digit).



-- Warning :  it is `exponentially' expensive in performance ----
--
showInBase : (base : ℕ)
             {base≥2 : True (2 ≤? base)}
             {base≤16 : True (base ≤? 16)} →
             ℕ → String
showInBase base {base≥2} {base≤16} n =
  String.fromList $
  map (showDigit {base≤16 = base≤16}) $
  reverse $
  proj₁ $ toDigits base {base≥2 = base≥2} n
------------------------------------------------------------------

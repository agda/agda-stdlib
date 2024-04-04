------------------------------------------------------------------------
-- The Agda standard library
--
-- Digits and digit expansions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Digit where

open import Data.Nat.Base
  using (ℕ; zero; suc; _<_; _/_; _%_; sz<ss; _+_; _*_; 2+; _≤′_)
open import Data.Nat.Properties
  using (_≤?_; _<?_; ≤⇒≤′; module ≤-Reasoning; m≤m+n; +-comm; +-assoc;
    *-distribˡ-+; *-identityʳ)
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; replicate; [_]; _∷_; [])
open import Data.Product.Base using (∃; _,_)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Nat.DivMod using (m/n<m; _divMod_; result)
open import Data.Nat.Induction
  using (Acc; acc; <-wellFounded-fast; <′-Rec; <′-rec)
open import Function.Base using (_$_)
open import Relation.Nullary.Decidable using (True; does; toWitness)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ → Set
Digit b = Fin b

-- Some specific digit kinds.

Decimal = Digit 10
Bit     = Digit 2

-- Some named digits.

0b : Bit
0b = zero

1b : Bit
1b = suc zero

------------------------------------------------------------------------
-- Converting between `ℕ` and `expansions of ℕ`

toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
toNatDigits base@(suc zero)    n = replicate n 1
toNatDigits base@(suc (suc _)) n = aux (<-wellFounded-fast n) []
  where
  aux : {n : ℕ} → Acc _<_ n → List ℕ → List ℕ
  aux {zero}        _      xs =  (0 ∷ xs)
  aux {n@(suc _)} (acc wf) xs with does (0 <? n / base)
  ... | false = (n % base) ∷ xs -- Could this more simply be n ∷ xs here?
  ... | true  = aux (wf (m/n<m n base sz<ss)) ((n % base) ∷ xs)

------------------------------------------------------------------------
-- Converting between `ℕ` and expansions of `Digit base`

Expansion : ℕ → Set
Expansion base = List (Digit base)

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : ∀ {base} → Expansion base → ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + fromDigits ds * base

-- toDigits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) →
           ∃ λ (ds : Expansion base) → fromDigits ds ≡ n
toDigits base@(suc (suc k)) n = <′-rec Pred helper n
  where

  Pred = λ n → ∃ λ ds → fromDigits ds ≡ n

  cons : ∀ {m} (r : Digit base) → Pred m → Pred (toℕ r + m * base)
  cons r (ds , eq) = (r ∷ ds , cong (λ i → toℕ r + i * base) eq)

  lem′ : ∀ x k → x + x + (k + x * k) ≡ k + x * 2+ k
  lem′ x k = begin
    x + x + (k + x * k)   ≡⟨ +-assoc (x + x) k _ ⟨
    x + x + k + x * k     ≡⟨ cong (_+ x * k) (+-comm _ k) ⟩
    k + (x + x) + x * k   ≡⟨ +-assoc k (x + x) _ ⟩
    k + ((x + x) + x * k) ≡⟨ cong (k +_) (begin
      (x + x) + x * k       ≡⟨ +-assoc x x _ ⟩
      x + (x + x * k)       ≡⟨ cong (x +_) (cong (_+ x * k) (*-identityʳ x)) ⟨
      x + (x * 1 + x * k)   ≡⟨ cong₂ _+_ (*-identityʳ x) (*-distribˡ-+ x 1 k ) ⟨
      x * 1 + (x * suc k)   ≡⟨ *-distribˡ-+ x 1 (1 + k) ⟨
      x * 2+ k              ∎) ⟩
    k + x * 2+ k          ∎
    where open ≡-Reasoning

  lem : ∀ x k r → 2 + x ≤′ r + (1 + x) * (2 + k)
  lem x k r = ≤⇒≤′ $ begin
    2 + x                             ≤⟨ m≤m+n _ _ ⟩
    2 + x + (x + (1 + x) * k + r)     ≡⟨ cong ((2 + x) +_) (+-comm _ r) ⟩
    2 + x + (r + (x + (1 + x) * k))   ≡⟨ +-assoc (2 + x) r _ ⟨
    2 + x + r + (x + (1 + x) * k)     ≡⟨ cong (_+ (x + (1 + x) * k)) (+-comm (2 + x) r) ⟩
    r + (2 + x) + (x + (1 + x) * k)   ≡⟨ +-assoc r (2 + x) _ ⟩
    r + ((2 + x) + (x + (1 + x) * k)) ≡⟨ cong (r +_) (cong 2+ (+-assoc x x _)) ⟨
    r + (2 + (x + x + (1 + x) * k))   ≡⟨ cong (λ z → r + (2+ z)) (lem′ x k) ⟩
    r + (2 + (k + x * (2 + k)))       ≡⟨⟩
    r + (1 + x) * (2 + k)             ∎
    where open ≤-Reasoning

  helper : ∀ n → <′-Rec Pred n → Pred n
  helper n                       rec with n divMod base
  ... | result zero    r eq = ([ r ] , sym eq)
  ... | result (suc x) r refl = cons r (rec (lem x k (toℕ r)))

------------------------------------------------------------------------
-- Showing digits

-- The characters used to show the first 16 digits.

digitChars : Vec Char 16
digitChars =
  '0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷
  'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ []

-- showDigit shows digits in base ≤ 16.

showDigit : ∀ {base} {base≤16 : True (base ≤? 16)} → Digit base → Char
showDigit {base≤16 = base≤16} d =
  Vec.lookup digitChars (Fin.inject≤ d (toWitness base≤16))

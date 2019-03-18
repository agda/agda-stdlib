------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Base where

open import Function using (id)
open import Data.Integer as ℤ using (ℤ; ∣_∣; +_; -[1+_])
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (_∣_ ; divides ; ∣-antisym)
open import Data.Nat.Coprimality as C using (Coprime; coprime?; Bézout-coprime)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Product
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable
  using (True; False; toWitness)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; Decidable; _⇒_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; subst; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

------------------------------------------------------------------------
-- Rational numbers in reduced form. Note that there is exactly one
-- way to represent every rational number.

record ℚ : Set where
  constructor mkℚ
  field
    numerator     : ℤ
    denominator-1 : ℕ
    .isCoprime    : Coprime ∣ numerator ∣ (suc denominator-1)

  denominator : ℤ
  denominator = + suc denominator-1

open ℚ public using ()
  renaming
  ( numerator   to ↥_
  ; denominator to ↧_
  )

------------------------------------------------------------------------
-- Equality of rational numbers (coincides with _≡_)

infix 4 _≃_

_≃_ : Rel ℚ 0ℓ
p ≃ q = (↥ p ℤ.* ↧ q) ≡ (↥ q) ℤ.* (↧ p)

------------------------------------------------------------------------
-- Ordering of rationals

infix 4 _≤_

data _≤_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p) → p ≤ q

------------------------------------------------------------------------
-- Two useful lemmas to help with constructing on rationals
--
-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

infix 4 _≢0
_≢0 : ℕ → Set
n ≢0 = False (n ℕ.≟ 0)

-- introducing a notation for that nasty pattern
pattern ⟨_&_∧_&_⟩ p eqp q eqq = GCD.is (divides p eqp , divides q eqq) _

normalize : ∀ m n g .{m≢0 : m ≢0} .{n≢0 : n ≢0} .{g≢0 : g ≢0} → GCD m n g →
            Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] Coprime (suc p) (suc q) × m ℕ.* suc q ≡ n ℕ.* suc p
normalize 0       n       g {m≢0 = ()} _
normalize m       0       g {n≢0 = ()} _
normalize m       n       0 {g≢0 = ()} _
normalize (suc _) n       g          ⟨ 0     & ()    ∧ q     & n≡qg' ⟩
normalize m       (suc _) g          ⟨ p     & m≡pg' ∧ 0     & () ⟩
normalize(suc _)  (suc _) (suc g) G@(⟨ suc p & refl  ∧ suc q & refl ⟩)
  = p , q , Bézout-coprime (Bézout.identity G) , (begin
    (suc p ℕ.* suc g) ℕ.* suc q ≡⟨ ℕ.*-assoc (suc p) (suc g) (suc q) ⟩
    suc p ℕ.* (suc g ℕ.* suc q) ≡⟨ cong (suc p ℕ.*_) (ℕ.*-comm (suc g) (suc q)) ⟩
    suc p ℕ.* (suc q ℕ.* suc g) ≡⟨ ℕ.*-comm (suc p) _ ⟩
    (suc q ℕ.* suc g) ℕ.* suc p ∎)

-- a version of gcd that returns a proof that the result is non-zero given
-- that one of the inputs is non-zero

gcd≢0 : (m n : ℕ) {m≢0 : m ≢0} → Σ[ d ∈ ℕ ] GCD m n d × d ≢0
gcd≢0 m  n {m≢0} with gcd m n
... | (suc d , G)  = (suc d , G , tt)
... | (0 , GCD.is (0|m , _) _) with ℕDiv.0∣⇒≡0 0|m
...   | refl = contradiction m≢0 id

pattern +0       = + 0
pattern +[1+_] n = + suc n

norm-mkℚ : (n : ℤ) (d : ℕ) → .{d≢0 : d ≢0} → ℚ
norm-mkℚ +0       d {d≢0} = mkℚ +0 0 (C.sym (C.1-coprimeTo 0))
norm-mkℚ -[1+ n ] d {d≢0} =
  let (q , gcd , q≢0)      = gcd≢0 (suc n) d
      (n′ , d′ , prf , eq) = normalize (suc n) d q {_} {d≢0} {q≢0} gcd
  in mkℚ -[1+ n′ ] d′ prf
norm-mkℚ +[1+ n ] d {d≢0} =
  let (q , gcd , q≢0)      = gcd≢0 (suc n) d
      (n′ , d′ , prf , eq) = normalize (suc n) d q {_} {d≢0} {q≢0} gcd
  in mkℚ (+ suc n′) d′ prf

------------------------------------------------------------------------------
-- Operations on rationals

infix  8 -_ 1/_
infixl 7 _*_ _/_ _÷_
infixl 6 _-_ _+_

-- unary negation

-_ : ℚ → ℚ
- mkℚ -[1+ n ] d prf = mkℚ +[1+ n ] d prf
- mkℚ +0       d prf = mkℚ +0       d prf
- mkℚ +[1+ n ] d prf = mkℚ -[1+ n ] d prf

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚ) → .{n≢0 : ∣ ↥ p ∣ ≢0} → ℚ
(1/ mkℚ +0 d prf) {()}
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

-- multiplication

_*_ : ℚ → ℚ → ℚ
mkℚ n₁ d₁ prf₁ * mkℚ n₂ d₂ prf₂ = norm-mkℚ (n₁ ℤ.* n₂) (suc d₁ ℕ.* suc d₂)

-- division

_÷_ : (numerator : ℤ) (denominator : ℕ)
      .{coprime : True (coprime? ∣ numerator ∣ denominator)}
      {≢0 : denominator ≢0} →
      ℚ
(n ÷ zero)  {≢0 = ()}
(n ÷ suc d) {c} = mkℚ n d (toWitness c)

-- addition

_+_ : ℚ → ℚ → ℚ
mkℚ n₁ d₁ prf₁ + mkℚ n₂ d₂ prf₂ = norm-mkℚ
  (n₁ ℤ.* (+[1+ d₂ ]) ℤ.+ n₂ ℤ.* (+[1+ d₂ ]))
  (suc d₁ ℕ.* suc d₂)

-- subtraction

_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

-- division

_/_ : (p q : ℚ) → {n≢0 : ∣ ↥ q ∣ ≢0} → ℚ
(p / q) {n≢0} = p * (1/_ q {n≢0})

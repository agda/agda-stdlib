------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Coprimality where

open import Data.Empty
open import Data.Fin.Base using (toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Product as Prod
open import Function
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_; _≢_; refl; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary as Nullary hiding (recompute)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition
--
-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common divisor is 1.

Coprime : Rel ℕ 0ℓ
Coprime m n = ∀ {i} → i ∣ m × i ∣ n → i ≡ 1

------------------------------------------------------------------------
-- Relationship between GCD and coprimality

coprime⇒GCD≡1 : ∀ {m n} → Coprime m n → GCD m n 1
coprime⇒GCD≡1 {m} {n} c = GCD.is (1∣ m , 1∣ n) (∣-reflexive ∘ c)

GCD≡1⇒coprime : ∀ {m n} → GCD m n 1 → Coprime m n
GCD≡1⇒coprime g cd with GCD.greatest g cd
... | divides q eq = m*n≡1⇒n≡1 q _ (P.sym eq)

coprime⇒gcd≡1 : ∀ {m n} → Coprime m n → gcd m n ≡ 1
coprime⇒gcd≡1 coprime = GCD.unique (gcd-GCD _ _) (coprime⇒GCD≡1 coprime)

gcd≡1⇒coprime : ∀ {m n} → gcd m n ≡ 1 → Coprime m n
gcd≡1⇒coprime gcd≡1 = GCD≡1⇒coprime (subst (GCD _ _) gcd≡1 (gcd-GCD _ _))

coprime-/gcd : ∀ m n .{{_ : NonZero (gcd m n)}} →
               Coprime (m / gcd m n) (n / gcd m n)
coprime-/gcd m n = GCD≡1⇒coprime (GCD-/gcd m n)

------------------------------------------------------------------------
-- Relational properties of Coprime

sym : Symmetric Coprime
sym c = c ∘ swap

private
  0≢1 : 0 ≢ 1
  0≢1 ()

  2+≢1 : ∀ {n} → suc (suc n) ≢ 1
  2+≢1 ()

coprime? : Decidable Coprime
coprime? i j with mkGCD i j
... | (0           , g) = no  (0≢1  ∘ GCD.unique g ∘ coprime⇒GCD≡1)
... | (1           , g) = yes (GCD≡1⇒coprime g)
... | (suc (suc d) , g) = no  (2+≢1 ∘ GCD.unique g ∘ coprime⇒GCD≡1)

------------------------------------------------------------------------
-- Other basic properties

-- Everything is coprime to 1.

1-coprimeTo : ∀ m → Coprime 1 m
1-coprimeTo m = ∣1⇒≡1 ∘ proj₁

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-m⇒m≡1 : ∀ {m} → Coprime 0 m → m ≡ 1
0-coprimeTo-m⇒m≡1 {m} c = c (m ∣0 , ∣-refl)

¬0-coprimeTo-2+ : ∀ {n} → ¬ Coprime 0 (2 + n)
¬0-coprimeTo-2+ coprime = contradiction (0-coprimeTo-m⇒m≡1 coprime) λ()

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : ∀ {m n} → Coprime m n → Coprime (n + m) n
coprime-+ c (d₁ , d₂) = c (∣m+n∣m⇒∣n d₁ d₂ , d₂)

-- Recomputable

recompute : ∀ {n d} → .(Coprime n d) → Coprime n d
recompute {n} {d} c = Nullary.recompute (coprime? n d) c

------------------------------------------------------------------------
-- Relationship with Bezout's lemma

-- If the "gcd" in Bézout's identity is non-zero, then the "other"
-- divisors are coprime.

Bézout-coprime : ∀ {i j d} .{{_ : NonZero d}} →
                 Bézout.Identity d (i * d) (j * d) → Coprime i j
Bézout-coprime {d = suc _} (Bézout.+- x y eq) (divides q₁ refl , divides q₂ refl) =
  lem₁₀ y q₂ x q₁ eq
Bézout-coprime {d = suc _} (Bézout.-+ x y eq) (divides q₁ refl , divides q₂ refl) =
  lem₁₀ x q₁ y q₂ eq

-- Coprime numbers satisfy Bézout's identity.

coprime-Bézout : ∀ {i j} → Coprime i j → Bézout.Identity 1 i j
coprime-Bézout = Bézout.identity ∘ coprime⇒GCD≡1

-- If i divides jk and is coprime to j, then it divides k.

coprime-divisor : ∀ {k i j} → Coprime i j → i ∣ j * k → i ∣ k
coprime-divisor {k} c (divides q eq′) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * k ∸ y * q) (lem₈ x y eq eq′)
... | Bézout.-+ x y eq = divides (y * q ∸ x * k) (lem₉ x y eq eq′)

-- If d is a common divisor of mk and nk, and m and n are coprime,
-- then d divides k.

coprime-factors : ∀ {d m n k} →
                  Coprime m n → d ∣ m * k × d ∣ n * k → d ∣ k
coprime-factors c (divides q₁ eq₁ , divides q₂ eq₂) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * q₁ ∸ y * q₂) (lem₁₁ x y eq eq₁ eq₂)
... | Bézout.-+ x y eq = divides (y * q₂ ∸ x * q₁) (lem₁₁ y x eq eq₂ eq₁)

------------------------------------------------------------------------
-- Primality implies coprimality.

prime⇒coprime : ∀ m → Prime m →
                ∀ n → 0 < n → n < m → Coprime m n
prime⇒coprime (suc (suc _)) p _ _ _ {0} (0∣m , _) =
  contradiction (0∣⇒≡0 0∣m) λ()
prime⇒coprime (suc (suc _)) _ _ _ _ {1} _         = refl
prime⇒coprime (suc (suc _)) p (suc _) _ n<m {(suc (suc _))} (d∣m , d∣n) =
  contradiction d∣m (p 2≤d d<m)
  where 2≤d = s≤s (s≤s z≤n); d<m = <-transˡ (s≤s (∣⇒≤ d∣n)) n<m

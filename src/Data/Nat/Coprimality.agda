------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Coprimality where

open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; NonZero; NonTrivial; nonTrivial⇒≢1)
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.GCD.Lemmas using (lem₁₀; lem₁₁; lem₈; lem₉)
open import Data.Nat.Primality using (Prime; prime⇒irreducible)
open import Data.Nat.Properties
open import Data.Nat.DivMod using (_/_; n/1≡n; /-congˡ; /-congʳ; m*n/n≡m)
open import Data.Product.Base as Prod using (proj₁; proj₂; _,_; ∃; _×_; swap)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; trans; cong; subst)
open import Relation.Nullary as Nullary using (¬_; contradiction; map′)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Symmetric; Decidable)

private
  variable d m n o p : ℕ

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition
--
-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common divisor is 1.

Coprime : Rel ℕ 0ℓ
Coprime m n = ∀ {d} → d ∣ m × d ∣ n → d ≡ 1

------------------------------------------------------------------------
-- Relationship between GCD and coprimality

coprime⇒GCD≡1 : Coprime m n → GCD m n 1
coprime⇒GCD≡1 {m} {n} coprime = GCD.is (1∣ m , 1∣ n) (∣-reflexive ∘ coprime)

GCD≡1⇒coprime : GCD m n 1 → Coprime m n
GCD≡1⇒coprime g cd with divides q eq ← GCD.greatest g cd
  = m*n≡1⇒n≡1 q _ (≡.sym eq)

coprime⇒gcd≡1 : Coprime m n → gcd m n ≡ 1
coprime⇒gcd≡1 coprime = GCD.unique (gcd-GCD _ _) (coprime⇒GCD≡1 coprime)

gcd≡1⇒coprime : gcd m n ≡ 1 → Coprime m n
gcd≡1⇒coprime gcd≡1 = GCD≡1⇒coprime (subst (GCD _ _) gcd≡1 (gcd-GCD _ _))

coprime-/gcd : ∀ m n .{{_ : NonZero (gcd m n)}} →
               Coprime (m / gcd m n) (n / gcd m n)
coprime-/gcd m n = GCD≡1⇒coprime (GCD-/gcd m n)

------------------------------------------------------------------------
-- Relational properties of Coprime

sym : Symmetric Coprime
sym c = c ∘ swap

coprime? : Decidable Coprime
coprime? m n = map′ gcd≡1⇒coprime coprime⇒gcd≡1 (gcd m n ≡? 1)

------------------------------------------------------------------------
-- Other basic properties

-- Everything is coprime to 1.

1-coprimeTo : ∀ m → Coprime 1 m
1-coprimeTo m = ∣1⇒≡1 ∘ proj₁

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-m⇒m≡1 : Coprime 0 m → m ≡ 1
0-coprimeTo-m⇒m≡1 {m} coprime = coprime (m ∣0 , ∣-refl)

¬0-coprimeTo-2+ : .{{NonTrivial n}} → ¬ Coprime 0 n
¬0-coprimeTo-2+ {n} coprime = contradiction (0-coprimeTo-m⇒m≡1 coprime) (nonTrivial⇒≢1 {n})

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : Coprime m n → Coprime (n + m) n
coprime-+ coprime (d₁ , d₂) = coprime (∣m+n∣m⇒∣n d₁ d₂ , d₂)

-- Recomputable

recompute : .(Coprime n d) → Coprime n d
recompute {n} {d} coprime = Nullary.recompute (coprime? n d) coprime

------------------------------------------------------------------------
-- Relationship with Bezout's lemma

-- If the "gcd" in Bézout's identity is non-zero, then the "other"
-- divisors are coprime.

Bézout-coprime : .{{NonZero d}} →
                 Bézout.Identity d (m * d) (n * d) → Coprime m n
Bézout-coprime {d = suc _} (Bézout.+- x y eq) (divides-refl q₁ , divides-refl q₂) =
  lem₁₀ y q₂ x q₁ eq
Bézout-coprime {d = suc _} (Bézout.-+ x y eq) (divides-refl q₁ , divides-refl q₂) =
  lem₁₀ x q₁ y q₂ eq

-- Coprime numbers satisfy Bézout's identity.

coprime-Bézout : Coprime m n → Bézout.Identity 1 m n
coprime-Bézout = Bézout.identity ∘ coprime⇒GCD≡1

-- If m divides n*o and is coprime to n, then it divides o.

coprime-divisor : Coprime m n → m ∣ n * o → m ∣ o
coprime-divisor {o = o} c (divides q eq′) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * o ∸ y * q) (lem₈ x y eq eq′)
... | Bézout.-+ x y eq = divides (y * q ∸ x * o) (lem₉ x y eq eq′)

-- If d is a common divisor of m*o and n*o, and m and n are coprime,
-- then d divides o.

coprime-factors : Coprime m n → d ∣ m * o × d ∣ n * o → d ∣ o
coprime-factors c (divides q₁ eq₁ , divides q₂ eq₂) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * q₁ ∸ y * q₂) (lem₁₁ x y eq eq₁ eq₂)
... | Bézout.-+ x y eq = divides (y * q₂ ∸ x * q₁) (lem₁₁ y x eq eq₂ eq₁)

------------------------------------------------------------------------
-- Primality implies coprimality.

prime⇒coprime : Prime p → .{{NonZero n}} → n < p → Coprime p n
prime⇒coprime p n<p (d∣p , d∣n) with prime⇒irreducible p d∣p
... | inj₁ d≡1      = d≡1
... | inj₂ d≡p@refl = contradiction n<p (≤⇒≯ (∣⇒≤ d∣n))

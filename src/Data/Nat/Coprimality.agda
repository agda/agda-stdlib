------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

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
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; subst; module ≡-Reasoning)
open import Relation.Nullary
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

coprime-/gcd : ∀ m n {gcd≢0} →
               Coprime ((m / gcd m n) {gcd≢0}) ((n / gcd m n) {gcd≢0})
coprime-/gcd m n {gcd≢0} = GCD≡1⇒coprime (GCD-/gcd m n {gcd≢0})

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

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : ∀ {m n} → Coprime m n → Coprime (n + m) n
coprime-+ c (d₁ , d₂) = c (∣m+n∣m⇒∣n d₁ d₂ , d₂)

------------------------------------------------------------------------
-- Relationship with Bezout's lemma

-- If the "gcd" in Bézout's identity is non-zero, then the "other"
-- divisors are coprime.

Bézout-coprime : ∀ {i j d} →
                 Bézout.Identity (suc d) (i * suc d) (j * suc d) →
                 Coprime i j
Bézout-coprime (Bézout.+- x y eq) (divides q₁ refl , divides q₂ refl) =
  lem₁₀ y q₂ x q₁ eq
Bézout-coprime (Bézout.-+ x y eq) (divides q₁ refl , divides q₂ refl) =
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
prime⇒coprime (suc (suc m)) _  _ _  _ {1} _                       = refl
prime⇒coprime (suc (suc m)) p  _ _  _ {0} (divides q 2+m≡q*0 , _) =
  ⊥-elim $ m+1+n≢m 0 (begin-equality
    2 + m  ≡⟨ 2+m≡q*0 ⟩
    q * 0  ≡⟨ *-zeroʳ q ⟩
    0      ∎)
prime⇒coprime (suc (suc m)) p (suc n) _ 1+n<2+m {suc (suc i)}
              (2+i∣2+m , 2+i∣1+n) =
  ⊥-elim (p _ 2+i′∣2+m)
  where
  i<m : i < m
  i<m = +-cancelˡ-< 2 (begin-strict
    2 + i ≤⟨ ∣⇒≤ 2+i∣1+n ⟩
    1 + n <⟨ 1+n<2+m ⟩
    2 + m ∎)

  2+i′∣2+m : 2 + toℕ (fromℕ< i<m) ∣ 2 + m
  2+i′∣2+m = subst (_∣ 2 + m)
    (P.sym (cong (2 +_) (toℕ-fromℕ< i<m)))
    2+i∣2+m


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use GCD from `Data.Nat.GCD` as continued support for the
-- proofs below is not guaranteed.

-- Version 1.1.

data GCD′ : ℕ → ℕ → ℕ → Set where
  gcd-* : ∀ {d} q₁ q₂ (c : Coprime q₁ q₂) →
          GCD′ (q₁ * d) (q₂ * d) d
{-# WARNING_ON_USAGE GCD′
"Warning: GCD′ was deprecated in v1.1."
#-}
gcd-gcd′ : ∀ {d m n} → GCD m n d → GCD′ m n d
gcd-gcd′         g with GCD.commonDivisor g
gcd-gcd′ {zero}  g | (divides q₁ refl , divides q₂ refl)
  with q₁ * 0 | *-comm 0 q₁ | q₂ * 0 | *-comm 0 q₂
... | .0 | refl | .0 | refl = gcd-* 1 1 (1-coprimeTo 1)
gcd-gcd′ {suc d} g | (divides q₁ refl , divides q₂ refl) =
  gcd-* q₁ q₂ (Bézout-coprime (Bézout.identity g))
{-# WARNING_ON_USAGE gcd-gcd′
"Warning: gcd-gcd′ was deprecated in v1.1."
#-}
gcd′-gcd : ∀ {m n d} → GCD′ m n d → GCD m n d
gcd′-gcd (gcd-* q₁ q₂ c) = GCD.is (n∣m*n q₁ , n∣m*n q₂) (coprime-factors c)
{-# WARNING_ON_USAGE gcd′-gcd
"Warning: gcd′-gcd was deprecated in v1.1."
#-}
mkGCD′ : ∀ m n → ∃ λ d → GCD′ m n d
mkGCD′ m n = Prod.map id gcd-gcd′ (mkGCD m n)
{-# WARNING_ON_USAGE mkGCD′
"Warning: mkGCD′ was deprecated in v1.1."
#-}

-- Version 1.2

coprime-gcd = coprime⇒GCD≡1
{-# WARNING_ON_USAGE coprime-gcd
"Warning: coprime-gcd was deprecated in v1.2.
Please use coprime⇒GCD≡1 instead."
#-}
gcd-coprime = GCD≡1⇒coprime
{-# WARNING_ON_USAGE gcd-coprime
"Warning: gcd-coprime was deprecated in v1.2.
Please use GCD≡1⇒coprime instead."
#-}

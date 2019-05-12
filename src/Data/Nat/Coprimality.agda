------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Coprimality where

open import Data.Empty
open import Data.Fin using (toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Product as Prod
open import Function
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; subst; module ≡-Reasoning)
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common divisor is 1.

Coprime : Rel ℕ 0ℓ
Coprime m n = ∀ {i} → i ∣ m × i ∣ n → i ≡ 1

------------------------------------------------------------------------
-- Relationship between GCD and coprimality

coprime-gcd : ∀ {m n} → Coprime m n → GCD m n 1
coprime-gcd {m} {n} c = GCD.is (1∣ m , 1∣ n) greatest
  where
  greatest : ∀ {d} → d ∣ m × d ∣ n → d ∣ 1
  greatest cd with c cd
  ... | refl = 1∣ 1

gcd-coprime : ∀ {m n} → GCD m n 1 → Coprime m n
gcd-coprime g cd with GCD.greatest g cd
... | divides q eq = m*n≡1⇒n≡1 q _ (P.sym eq)

------------------------------------------------------------------------
-- Coprime is decidable.

private
  0≢1 : 0 ≢ 1
  0≢1 ()

  2+≢1 : ∀ {n} → suc (suc n) ≢ 1
  2+≢1 ()

coprime? : Decidable Coprime
coprime? i j with gcd i j
... | (0           , g) = no  (0≢1  ∘ GCD.unique g ∘ coprime-gcd)
... | (1           , g) = yes (gcd-coprime g)
... | (suc (suc d) , g) = no  (2+≢1 ∘ GCD.unique g ∘ coprime-gcd)

-- The coprimality relation is symmetric.

sym : Symmetric Coprime
sym c = c ∘ swap

-- Everything is coprime to 1.

1-coprimeTo : ∀ m → Coprime 1 m
1-coprimeTo m = ∣1⇒≡1 ∘ proj₁

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-m⇒m≡1 : ∀ {m} → Coprime 0 m → m ≡ 1
0-coprimeTo-m⇒m≡1 {m} c = c (m ∣0 , ∣-refl)

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : ∀ {m n} → Coprime m n → Coprime (n + m) n
coprime-+ c (d₁ , d₂) = c (∣m+n∣m⇒∣n d₁ d₂ , d₂)

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
coprime-Bézout = Bézout.identity ∘ coprime-gcd

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

-- A variant of GCD.

data GCD′ : ℕ → ℕ → ℕ → Set where
  gcd-* : ∀ {d} q₁ q₂ (c : Coprime q₁ q₂) →
          GCD′ (q₁ * d) (q₂ * d) d

-- The two definitions are equivalent.

gcd-gcd′ : ∀ {d m n} → GCD m n d → GCD′ m n d
gcd-gcd′         g with GCD.commonDivisor g
gcd-gcd′ {zero}  g | (divides q₁ refl , divides q₂ refl)
  with q₁ * 0 | *-comm 0 q₁ | q₂ * 0 | *-comm 0 q₂
... | .0 | refl | .0 | refl = gcd-* 1 1 (1-coprimeTo 1)
gcd-gcd′ {suc d} g | (divides q₁ refl , divides q₂ refl) =
  gcd-* q₁ q₂ (Bézout-coprime (Bézout.identity g))

gcd′-gcd : ∀ {m n d} → GCD′ m n d → GCD m n d
gcd′-gcd (gcd-* q₁ q₂ c) = GCD.is (n∣m*n q₁ , n∣m*n q₂) (coprime-factors c)

-- Calculates (the alternative representation of) the gcd of the
-- arguments.

gcd′ : ∀ m n → ∃ λ d → GCD′ m n d
gcd′ m n = Prod.map id gcd-gcd′ (gcd m n)

-- Primality implies coprimality.

prime⇒coprime : ∀ m → Prime m →
                ∀ n → 0 < n → n < m → Coprime m n
prime⇒coprime (suc (suc m)) _  _ _  _ {1} _                       = refl
prime⇒coprime (suc (suc m)) p  _ _  _ {0} (divides q 2+m≡q*0 , _) =
  ⊥-elim $ m+1+n≢m 0 (begin
    2 + m  ≡⟨ 2+m≡q*0 ⟩
    q * 0  ≡⟨ *-zeroʳ q ⟩
    0      ∎)
  where open ≡-Reasoning
prime⇒coprime (suc (suc m)) p (suc n) _ 1+n<2+m {suc (suc i)}
              (2+i∣2+m , 2+i∣1+n) =
  ⊥-elim (p _ 2+i′∣2+m)
  where
  i<m : i < m
  i<m = +-cancelˡ-< 2 (begin-strict
    2 + i ≤⟨ ∣⇒≤ 2+i∣1+n ⟩
    1 + n <⟨ 1+n<2+m ⟩
    2 + m ∎)
    where open ≤-Reasoning

  2+i′∣2+m : 2 + toℕ (fromℕ≤ i<m) ∣ 2 + m
  2+i′∣2+m = subst (_∣ 2 + m)
    (P.sym (cong (2 +_) (toℕ-fromℕ≤ i<m)))
    2+i∣2+m

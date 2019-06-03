------------------------------------------------------------------------
-- The Agda standard library
--
-- Least common multiple
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.LCM where

open import Algebra
open import Data.Nat
open import Data.Nat.Coprimality as Coprime
  using (Coprime; mkGCD′; gcd-*; coprime-divisor)
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Nat.GCD
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open +-*-Solver

private
  gcd≢0′ : ∀ m {n} → False (gcd (suc m) (suc n) ≟ 0)
  gcd≢0′ m {n} = fromWitnessFalse (gcd≢0 (suc m) (suc n) (inj₁ (λ())))

------------------------------------------------------------------------
-- Properties that need to be shifted

/n-pres-∣ : ∀ {m n c} → m ∣ c → n ∣ c → Coprime m n → m * n ∣ c
/n-pres-∣ {m} {n} {c} m∣c n∣c cop = {!!}

{-
∣-test : ∀ {m n o} → m ∣ n → n ∣ o → (n / m) ∣ o
∣-test = {!!}
-}

------------------------------------------------------------------------
-- Definition

abstract

  lcm : ℕ → ℕ → ℕ
  lcm zero        n           = zero
  lcm n           zero        = zero
  lcm m@(suc m-1) n@(suc n-1) = (m * n / gcd m n) {gcd≢0′ m-1}

------------------------------------------------------------------------
-- Properties

abstract

  m∣lcm[m,n] : ∀ m n → m ∣ lcm m n
  m∣lcm[m,n] zero      zero      = 0 ∣0
  m∣lcm[m,n] zero      (suc n)   = 0 ∣0
  m∣lcm[m,n] (suc m)   zero      = suc m ∣0
  m∣lcm[m,n] m@(suc m-1) n@(suc n-1) = begin
    m                  ∣⟨ m∣m*n _ ⟩
    m * (n / gcd m n)  ≡⟨ sym (*-/-assoc m (gcd≢0′ m-1) (gcd[m,n]∣n m n)) ⟩
    (m * n) / gcd m n  ∎
    where open ∣-Reasoning

  n∣lcm[m,n] : ∀ m n → n ∣ lcm m n
  n∣lcm[m,n] zero        zero        = 0 ∣0
  n∣lcm[m,n] zero        (suc n)     = suc n ∣0
  n∣lcm[m,n] (suc m)     zero        = 0 ∣0
  n∣lcm[m,n] m@(suc m-1) n@(suc n-1) = begin
    n                 ∣⟨ m∣m*n (m / gcd m n) ⟩
    n * (m / gcd m n) ≡⟨ sym (*-/-assoc n (gcd≢0′ m-1) (gcd[m,n]∣m m n)) ⟩
    n * m / gcd m n   ≡⟨ cong (λ v → (v / gcd m n) {gcd≢0′ m-1}) (*-comm n m) ⟩
    m * n / gcd m n   ∎
    where open ∣-Reasoning

  lcm-least : ∀ {m n c} → m ∣ c → n ∣ c → lcm m n ∣ c
  lcm-least {zero}  {zero}  {c} 0∣c _   = 0∣c
  lcm-least {zero}  {suc n} {c} 0∣c _   = 0∣c
  lcm-least {suc m} {zero}  {c} _   0∣c = 0∣c
  lcm-least {m@(suc m-1)} {n@(suc n-1)} {c} m∣c n∣c = begin
    m * n / gcd m n   ≡⟨ *-/-assoc m (gcd≢0′ m-1) (gcd[m,n]∣n m n) ⟩
    m * (n / gcd m n) ∣⟨ /n-pres-∣ m∣c {!!} {!!} ⟩
    c                 ∎
    where open ∣-Reasoning

lcm-comm : ∀ m n → lcm m n ≡ lcm n m
lcm-comm m n = ∣-antisym
  (lcm-least (n∣lcm[m,n] n m) (m∣lcm[m,n] n m))
  (lcm-least (n∣lcm[m,n] m n) (m∣lcm[m,n] m n))

lcm[0,n]≡0 : ∀ n → lcm 0 n ≡ 0
lcm[0,n]≡0 n = 0∣⇒≡0 (m∣lcm[m,n] 0 n)

lcm[n,0]≡0 : ∀ n → lcm n 0 ≡ 0
lcm[n,0]≡0 n = 0∣⇒≡0 (n∣lcm[m,n] n 0)

lcm-factorˡ : ∀ m n k → lcm (k * m) (k * n) ≡ k * lcm m n
lcm-factorˡ m n k = {!!}

lcm-factorʳ : ∀ m n k → lcm (m * k) (n * k) ≡ lcm m n * k
lcm-factorʳ m n k rewrite *-comm m k | *-comm n k | *-comm (lcm m n) k = lcm-factorˡ m n k

lcm-coprime : ∀ m n → Coprime m n → lcm m n ≡ m * n
lcm-coprime = {!!}

gcd*lcm : ∀ m n → gcd m n * lcm m n ≡ m * n
gcd*lcm zero n rewrite lcm[0,n]≡0 n | *-zeroʳ (gcd 0 n)             = refl
gcd*lcm m zero rewrite lcm[n,0]≡0 m | *-zeroʳ (gcd m 0) | *-zeroʳ m = refl
gcd*lcm m@(suc m-1) n@(suc n-1) = begin
  g * lcm m n                 ≡⟨ cong (g *_) (sym (cong₂ lcm (a/n*n≡a g∣m) (a/n*n≡a g∣n))) ⟩
  g * lcm (m/g * g) (n/g * g) ≡⟨ cong (g *_) (lcm-factorʳ m/g n/g g) ⟩
  g * (lcm m/g n/g * g)       ≡⟨ cong (g *_) (cong (_* g) (lcm-coprime m/g n/g {!!})) ⟩
  g * (m/g * n/g * g)         ≡⟨ cong (g *_) (*-assoc m/g n/g g) ⟩
  g * (m/g * (n/g * g))       ≡⟨ sym (*-assoc g m/g (n/g * g)) ⟩
  (g * m/g) * (n/g * g)       ≡⟨ cong₂ _*_ (n*[a/n]≡a g∣m) (a/n*n≡a g∣n) ⟩
  m * n                       ∎
  where
  open ≡-Reasoning
  g   = gcd m n
  m/g = (m / g) {gcd≢0′ m-1}; g∣m = gcd[m,n]∣m m n
  n/g = (n / g) {gcd≢0′ m-1}; g∣n = gcd[m,n]∣n m n

------------------------------------------------------------------------
-- Least common multiple (lcm).

module LCM where

  -- Specification of the least common multiple (lcm) of two natural
  -- numbers.

  record LCM (i j lcm : ℕ) : Set where
    field
      -- The lcm is a common multiple.
      commonMultiple : i ∣ lcm × j ∣ lcm

      -- The lcm divides all common multiples, i.e. the lcm is the least
      -- common multiple according to the partial order _∣_.
      least : ∀ {m} → i ∣ m × j ∣ m → lcm ∣ m

  open LCM public

  -- The lcm is unique.

  unique : ∀ {d₁ d₂ m n} → LCM m n d₁ → LCM m n d₂ → d₁ ≡ d₂
  unique d₁ d₂ = ∣-antisym (LCM.least d₁ (LCM.commonMultiple d₂))
                           (LCM.least d₂ (LCM.commonMultiple d₁))

open LCM public using (LCM) hiding (module LCM)

------------------------------------------------------------------------
-- Calculating the lcm

lcm-LCM : ∀ m n → LCM m n (lcm m n)
lcm-LCM m n = record
  { commonMultiple = m∣lcm[m,n] m n , n∣lcm[m,n] m n
  ; least          = uncurry′ lcm-least
  }

mkLCM : ∀ m n → ∃ λ d → LCM m n d
mkLCM m n = lcm m n , lcm-LCM m n

GCD*LCM : ∀ {m n g l} → GCD m n g → LCM m n l → m * n ≡ g * l
GCD*LCM {m} {n} {g} {l} gc lc = sym (begin
  g * l             ≡⟨ cong₂ _*_ (GCD.unique gc (gcd-GCD m n)) (LCM.unique lc (lcm-LCM m n)) ⟩
  gcd m n * lcm m n ≡⟨ gcd*lcm m n ⟩
  m * n             ∎)
  where open ≡-Reasoning

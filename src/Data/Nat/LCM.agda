------------------------------------------------------------------------
-- The Agda standard library
--
-- Least common multiple
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.LCM where

open import Algebra
open import Data.Nat.Base
open import Data.Nat.Coprimality using (Coprime)
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Nat.GCD
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

private
  -- instance
    gcd≢0ˡ : ∀ {m n} {{_ : NonZero m}} → NonZero (gcd m n)
    gcd≢0ˡ {m@(suc _)} {n} = ≢-nonZero (gcd[m,n]≢0 m n (inj₁ λ()))

------------------------------------------------------------------------
-- Definition

lcm : ℕ → ℕ → ℕ
lcm zero        n = zero
lcm m@(suc m-1) n = m * (n / gcd m n)
  where instance _ = gcd≢0ˡ {m} {n}

------------------------------------------------------------------------
-- Core properties

private
  rearrange : ∀ m n .{{_ : NonZero m}} →
              lcm m n ≡ (m * n / gcd m n) {{gcd≢0ˡ {m} {n}}}
  rearrange m@(suc _) n = sym (*-/-assoc m {{gcd≢0ˡ {m} {n}}} (gcd[m,n]∣n m n))

m∣lcm[m,n] : ∀ m n → m ∣ lcm m n
m∣lcm[m,n] zero      n = 0 ∣0
m∣lcm[m,n] m@(suc _) n = m∣m*n (n / gcd m n)
  where instance _ = gcd≢0ˡ {m} {n}

n∣lcm[m,n] : ∀ m n → n ∣ lcm m n
n∣lcm[m,n] zero        n = n ∣0
n∣lcm[m,n] m@(suc m-1) n = begin
  n                 ∣⟨  m∣m*n (m / gcd m n) ⟩
  n * (m / gcd m n) ≡˘⟨ *-/-assoc n (gcd[m,n]∣m m n) ⟩
  n * m / gcd m n   ≡⟨  cong (_/ gcd m n) (*-comm n m) ⟩
  m * n / gcd m n   ≡˘⟨ rearrange m n ⟩
  m * (n / gcd m n) ∎
  where open ∣-Reasoning; instance _ = gcd≢0ˡ {m} {n}


lcm-least : ∀ {m n c} → m ∣ c → n ∣ c → lcm m n ∣ c
lcm-least {zero}      {n} {c} 0∣c _   = 0∣c
lcm-least {m@(suc _)} {n} {c} m∣c n∣c = P.subst (_∣ c) (sym (rearrange m n))
  (m∣n*o⇒m/n∣o gcd[m,n]∣m*n mn∣c*gcd)
  where
  instance _ = gcd≢0ˡ {m} {n}

  open ∣-Reasoning
  gcd[m,n]∣m*n : gcd m n ∣ m * n
  gcd[m,n]∣m*n = ∣-trans (gcd[m,n]∣m m n) (m∣m*n n)

  mn∣c*gcd : m * n ∣ c * gcd m n
  mn∣c*gcd = begin
    m * n               ∣⟨  gcd-greatest (P.subst (_∣ c * m) (*-comm n m) (*-monoˡ-∣ m n∣c)) (*-monoˡ-∣ n m∣c) ⟩
    gcd (c * m) (c * n) ≡˘⟨ c*gcd[m,n]≡gcd[cm,cn] c m n ⟩
    c * gcd m n         ∎

------------------------------------------------------------------------
-- Other properties

-- Note that all other properties of `gcd` should be inferable from the
-- 3 core properties above.

gcd*lcm : ∀ m n → gcd m n * lcm m n ≡ m * n
gcd*lcm zero        n = *-zeroʳ (gcd 0 n)
gcd*lcm m@(suc m-1) n = trans (cong (gcd m n *_) (rearrange m n)) (m*[n/m]≡n (begin
  gcd m n ∣⟨ gcd[m,n]∣m m n ⟩
  m       ∣⟨ m∣m*n n ⟩
  m * n   ∎))
  where open ∣-Reasoning; instance gcd≢0 = gcd≢0ˡ {m} {n}

lcm[0,n]≡0 : ∀ n → lcm 0 n ≡ 0
lcm[0,n]≡0 n = 0∣⇒≡0 (m∣lcm[m,n] 0 n)

lcm[n,0]≡0 : ∀ n → lcm n 0 ≡ 0
lcm[n,0]≡0 n = 0∣⇒≡0 (n∣lcm[m,n] n 0)

lcm-comm : ∀ m n → lcm m n ≡ lcm n m
lcm-comm m n = ∣-antisym
  (lcm-least (n∣lcm[m,n] n m) (m∣lcm[m,n] n m))
  (lcm-least (n∣lcm[m,n] m n) (m∣lcm[m,n] m n))

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
-- Calculating the LCM

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

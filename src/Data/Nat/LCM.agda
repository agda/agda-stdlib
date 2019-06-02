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
open import Data.Sum using (inj₁)
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; cong₂; sym; module ≡-Reasoning)
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

  lcd-least : ∀ {m n c} → m ∣ c → n ∣ c → lcm m n ∣ c
  lcd-least {zero}  {zero}  {c} 0∣c _   = 0∣c
  lcd-least {zero}  {suc n} {c} 0∣c _   = 0∣c
  lcd-least {suc m} {zero}  {c} _   0∣c = 0∣c
  lcd-least {m@(suc m-1)} {n@(suc n-1)} {c} m∣c n∣c = begin
    m * n / gcd m n   ≡⟨ *-/-assoc m (gcd≢0′ m-1) (gcd[m,n]∣n m n) ⟩
    m * (n / gcd m n) ∣⟨ /n-pres-∣ m∣c {!!} {!!} ⟩
    c                 ∎
    where open ∣-Reasoning

lcd-comm : ∀ m n → lcm m n ≡ lcm n m
lcd-comm m n = ∣-antisym
  (lcd-least (n∣lcm[m,n] n m) (m∣lcm[m,n] n m))
  (lcd-least (n∣lcm[m,n] m n) (m∣lcm[m,n] m n))

gcd*lcm : ∀ m n → gcd m n * lcm m n ≡ m * n
gcd*lcm 0 n = {!!}
gcd*lcm m 0 = {!!}
gcd*lcm m@(suc m-1) n@(suc n-1) = begin
  g * lcm m n                 ≡⟨ cong (g *_) (cong₂ lcm {!!} {!!}) ⟩
  g * lcm (m/g * g) (n/g * g) ≡⟨ cong (g *_) {!!} ⟩
  g * (lcm m/g n/g * g)       ≡⟨ cong (g *_) (cong (_* g) {!!}) ⟩
  g * (m/g * n/g * g)         ≡⟨ cong (g *_) (*-assoc m/g n/g g) ⟩
  g * (m/g * (n/g * g))       ≡⟨ sym (*-assoc g m/g (n/g * g)) ⟩
  (g * m/g) * (n/g * g)       ≡⟨ cong₂ _*_ {!!} (a/n*n≡a {!gcd[m,n]∣n m n!}) ⟩
  m * n                       ∎
  where
  open ≡-Reasoning
  g   = gcd m n
  m/g = (m / g) {{!!}}
  n/g = (n / g) {{!!}}

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

private
  lem₁ = solve 3 (λ a b c → a :* b :* c  :=  b :* (a :* c)) refl
  lem₂ = solve 3 (λ a b c → a :* b :* c  :=  a :* (b :* c)) refl

  -- If these lemmas are inlined, then type checking takes a lot
  -- longer... (In the development version of Agda from 2009-05-21.)

  mult₁ : ∀ q₁ q₂ d → q₁ * d ∣ q₁ * q₂ * d
  mult₁ q₁ q₂ d = divides q₂ (lem₁ q₁ q₂ d)

  mult₂ : ∀ q₁ q₂ d → q₂ * d ∣ q₁ * q₂ * d
  mult₂ q₁ q₂ d = divides q₁ (lem₂ q₁ q₂ d)

-- The lcm can be calculated from the gcd.

mkLCM : (i j : ℕ) → ∃ λ d → LCM i j d
mkLCM i j with Coprime.mkGCD′ i j
mkLCM .(q₁ * d) .(q₂ * d) | (d , gcd-* q₁ q₂ q₁-q₂-coprime) =
  ( q₁ * q₂ * d
  , record { commonMultiple = (mult₁ q₁ q₂ d , mult₂ q₁ q₂ d)
           ; least          = least d
           }
  )
  where
  least : ∀ d {m} → q₁ * d ∣ m × q₂ * d ∣ m → q₁ * q₂ * d ∣ m
  least zero (divides q₃ refl , _) = begin
    q₁ * q₂ * 0    ∣⟨ (q₁ * q₂ * 0) ∣0 ⟩
    0              ≡⟨ solve 2 (λ a b → con 0  :=  a :* (b :* con 0))
                              refl q₃ q₁ ⟩
    q₃ * (q₁ * 0)  ∎
    where open ∣-Reasoning
  least (suc d) {m} (divides q₃ eq₃ , divides q₄ eq₄) =
    q₁q₂d′∣m q₃ eq₃ q₂∣q₃
    where
    open P.≡-Reasoning
    d′ = suc d

    q₂∣q₃ : q₂ ∣ q₃
    q₂∣q₃ = coprime-divisor (Coprime.sym q₁-q₂-coprime)
              (divides q₄ $ *-cancelʳ-≡ _ _ (begin
                 q₁ * q₃ * d′    ≡⟨ lem₁ q₁ q₃ d′ ⟩
                 q₃ * (q₁ * d′)  ≡⟨ sym eq₃ ⟩
                 m               ≡⟨ eq₄ ⟩
                 q₄ * (q₂ * d′)  ≡⟨ sym (lem₂ q₄ q₂ d′) ⟩
                 q₄ *  q₂ * d′   ∎))

    q₁q₂d′∣m : ∀ q₃ → m ≡ q₃ * (q₁ * d′) → q₂ ∣ q₃ → q₁ * q₂ * d′ ∣ m
    q₁q₂d′∣m .(q₅ * q₂) eq₃′ (divides q₅ refl) =
      divides q₅ (begin
        m                    ≡⟨ eq₃′ ⟩
        q₅ * q₂ * (q₁ * d′)  ≡⟨ solve 4 (λ q₁ q₂ q₅ d′ → q₅ :* q₂ :* (q₁ :* d′)
                                                     :=  q₅ :* (q₁ :* q₂ :* d′))
                                        refl q₁ q₂ q₅ d′ ⟩
        q₅ * (q₁ * q₂ * d′)  ∎)

------------------------------------------------------------------------
-- Properties

-- The product of the gcd and the lcm is the product of the two
-- numbers.
{-
gcd*lcm : ∀ {i j d m} → GCD i j d → LCM i j m → i * j ≡ d * m
gcd*lcm  {i}        {j}       {d}  {m}               g l with LCM.unique l (proj₂ (lcm i j))
gcd*lcm  {i}        {j}       {d} .{proj₁ (lcm i j)} g l | refl with mkGCD′ i j
gcd*lcm .{q₁ * d′} .{q₂ * d′} {d}                    g l | refl | (d′ , gcd-* q₁ q₂ q₁-q₂-coprime)
                                                           with GCD.unique g
                                                                  (gcd′-gcd (gcd-* q₁ q₂ q₁-q₂-coprime))
gcd*lcm .{q₁ * d}  .{q₂ * d}  {d}                    g l | refl | (.d , gcd-* q₁ q₂ q₁-q₂-coprime) | refl =
  solve 3 (λ q₁ q₂ d → q₁ :* d :* (q₂ :* d)
                   :=  d :* (q₁ :* q₂ :* d))
          refl q₁ q₂ d
-}

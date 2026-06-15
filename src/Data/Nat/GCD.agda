------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest common divisor
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.GCD where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Properties
open import Data.Nat.Induction
  using (Acc; acc; <′-Rec; <′-recBuilder; <-wellFounded-fast)
open import Data.Product.Base
  using (_×_; _,_; proj₂; proj₁; swap; uncurry′; ∃; map)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_$_; _∘_)
open import Induction using (build)
open import Induction.Lexicographic using (_⊗_; [_⊗_])
open import Relation.Binary.Definitions using (tri<; tri>; tri≈; Symmetric)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Nullary.Negation.Core using (contradiction)
import Relation.Nullary.Decidable as Dec

open import Algebra.Definitions {A = ℕ} _≡_ as Algebra
  using (Associative; Commutative; LeftIdentity; RightIdentity; LeftZero; RightZero; Zero)

------------------------------------------------------------------------
-- Definition

-- Calculated via Euclid's algorithm. In order to show progress,
-- avoiding the initial step where the first argument may increase, it
-- is necessary to first define a version `gcd′` which assumes that the
-- second argument is strictly smaller than the first. The full `gcd`
-- function then compares the two arguments and applies `gcd′`
-- accordingly.

gcd′ : ∀ m n → Acc _<_ m → n < m → ℕ
gcd′ m zero      _         _   = m
gcd′ m n@(suc _) (acc rec) n<m = gcd′ n (m % n) (rec n<m) (m%n<n m n)

gcd : ℕ → ℕ → ℕ
gcd m n with <-cmp m n
... | tri< m<n _ _ = gcd′ n m (<-wellFounded-fast n) m<n
... | tri≈ _ _ _   = m
... | tri> _ _ n<m = gcd′ m n (<-wellFounded-fast m) n<m

------------------------------------------------------------------------
-- Core properties of gcd′

gcd′[m,n]∣m,n : ∀ {m n} rec n<m → gcd′ m n rec n<m ∣ m × gcd′ m n rec n<m ∣ n
gcd′[m,n]∣m,n {m} {zero}      rec       n<m = ∣-refl , m ∣0
gcd′[m,n]∣m,n {m} {n@(suc _)} (acc rec) n<m
  with gcd∣n , gcd∣m%n ← gcd′[m,n]∣m,n (rec n<m) (m%n<n m n)
  = ∣n∣m%n⇒∣m gcd∣n gcd∣m%n , gcd∣n

gcd′-greatest : ∀ {m n c} rec n<m → c ∣ m → c ∣ n → c ∣ gcd′ m n rec n<m
gcd′-greatest {m} {zero}      rec       n<m c∣m c∣n = c∣m
gcd′-greatest {m} {n@(suc _)} (acc rec) n<m c∣m c∣n =
  gcd′-greatest (rec n<m) (m%n<n m n) c∣n (%-presˡ-∣ c∣m c∣n)

------------------------------------------------------------------------
-- Core properties of gcd

gcd[m,n]∣m : ∀ m n → gcd m n ∣ m
gcd[m,n]∣m m n with <-cmp m n
... | tri< n<m _ _ = proj₂ (gcd′[m,n]∣m,n {n} {m} _ _)
... | tri≈ _ _ _   = ∣-refl
... | tri> _ _ m<n = proj₁ (gcd′[m,n]∣m,n {m} {n} _ _)

gcd[m,n]∣n : ∀ m n → gcd m n ∣ n
gcd[m,n]∣n m n with <-cmp m n
... | tri< n<m _    _ = proj₁ (gcd′[m,n]∣m,n {n} {m} _ _)
... | tri≈ _ ≡.refl _ = ∣-refl
... | tri> _ _    m<n = proj₂ (gcd′[m,n]∣m,n {m} {n} _ _)

gcd-greatest : ∀ {m n c} → c ∣ m → c ∣ n → c ∣ gcd m n
gcd-greatest {m} {n} c∣m c∣n with <-cmp m n
... | tri< n<m _ _ = gcd′-greatest _ _ c∣n c∣m
... | tri≈ _ _ _   = c∣m
... | tri> _ _ m<n = gcd′-greatest _ _ c∣m c∣n

------------------------------------------------------------------------
-- Other properties

-- Note that all other properties of `gcd` should be inferable from the
-- 3 core properties above.

gcd[0,0]≡0 : gcd 0 0 ≡ 0
gcd[0,0]≡0 = ∣-antisym (gcd 0 0 ∣0) (gcd-greatest (0 ∣0) (0 ∣0))

gcd[m,n]≢0 : ∀ m n → m ≢ 0 ⊎ n ≢ 0 → gcd m n ≢ 0
gcd[m,n]≢0 m n (inj₁ m≢0) eq = m≢0 (0∣⇒≡0 (subst (_∣ m) eq (gcd[m,n]∣m m n)))
gcd[m,n]≢0 m n (inj₂ n≢0) eq = n≢0 (0∣⇒≡0 (subst (_∣ n) eq (gcd[m,n]∣n m n)))

gcd[m,n]≡0⇒m≡0 : ∀ {m n} → gcd m n ≡ 0 → m ≡ 0
gcd[m,n]≡0⇒m≡0 {zero}  {n} eq = ≡.refl
gcd[m,n]≡0⇒m≡0 {suc m} {n} eq = contradiction eq (gcd[m,n]≢0 (suc m) n (inj₁ λ()))

gcd[m,n]≡0⇒n≡0 : ∀ m {n} → gcd m n ≡ 0 → n ≡ 0
gcd[m,n]≡0⇒n≡0 m {zero}  eq = ≡.refl
gcd[m,n]≡0⇒n≡0 m {suc n} eq = contradiction eq (gcd[m,n]≢0 m (suc n) (inj₂ λ()))

gcd-comm : Commutative gcd
gcd-comm m n = ∣-antisym
  (gcd-greatest (gcd[m,n]∣n m n) (gcd[m,n]∣m m n))
  (gcd-greatest (gcd[m,n]∣n n m) (gcd[m,n]∣m n m))

gcd-assoc : Associative gcd
gcd-assoc m n p = ∣-antisym
  (gcd-greatest gcd[gcd[m,n],p]|m (gcd-greatest gcd[gcd[m,n],p]∣n gcd[gcd[m,n],p]∣p))
  (gcd-greatest (gcd-greatest gcd[m,gcd[n,p]]∣m gcd[m,gcd[n,p]]∣n) gcd[m,gcd[n,p]]∣p)
  where
    open ∣-Reasoning
    gcd[gcd[m,n],p]|m = begin
      gcd (gcd m n) p ∣⟨ gcd[m,n]∣m (gcd m n) p ⟩
      gcd m n         ∣⟨ gcd[m,n]∣m m n ⟩
      m               ∎
    gcd[gcd[m,n],p]∣n = begin
      gcd (gcd m n) p ∣⟨ gcd[m,n]∣m (gcd m n) p ⟩
      gcd m n         ∣⟨ gcd[m,n]∣n m n ⟩
      n               ∎
    gcd[gcd[m,n],p]∣p = gcd[m,n]∣n (gcd m n) p
    gcd[m,gcd[n,p]]∣m = gcd[m,n]∣m m (gcd n p)
    gcd[m,gcd[n,p]]∣n = begin
      gcd m (gcd n p) ∣⟨ gcd[m,n]∣n m (gcd n p) ⟩
      gcd n p         ∣⟨ gcd[m,n]∣m n p ⟩
      n               ∎
    gcd[m,gcd[n,p]]∣p = begin
      gcd m (gcd n p) ∣⟨ gcd[m,n]∣n m (gcd n p) ⟩
      gcd n p         ∣⟨ gcd[m,n]∣n n p ⟩
      p               ∎

gcd-identityˡ : LeftIdentity 0 gcd
gcd-identityˡ zero = ≡.refl
gcd-identityˡ (suc _) = ≡.refl

gcd-identityʳ : RightIdentity 0 gcd
gcd-identityʳ zero = ≡.refl
gcd-identityʳ (suc _) = ≡.refl

gcd-identity : Algebra.Identity 0 gcd
gcd-identity = gcd-identityˡ , gcd-identityʳ

gcd-zeroˡ : LeftZero 1 gcd
gcd-zeroˡ n = ∣-antisym gcd[1,n]∣1 1∣gcd[1,n]
  where
    gcd[1,n]∣1 = gcd[m,n]∣m 1 n
    1∣gcd[1,n] = 1∣ gcd 1 n

gcd-zeroʳ : RightZero 1 gcd
gcd-zeroʳ n = ∣-antisym gcd[n,1]∣1 1∣gcd[n,1]
  where
    gcd[n,1]∣1 = gcd[m,n]∣n n 1
    1∣gcd[n,1] = 1∣ gcd n 1

gcd-zero : Zero 1 gcd
gcd-zero = gcd-zeroˡ , gcd-zeroʳ

gcd-universality : ∀ {m n g} →
                   (∀ {d} → d ∣ m × d ∣ n → d ∣ g) →
                   (∀ {d} → d ∣ g → d ∣ m × d ∣ n) →
                   g ≡ gcd m n
gcd-universality {m} {n} forwards backwards with back₁ , back₂ ← backwards ∣-refl
  = ∣-antisym (gcd-greatest back₁ back₂) (forwards (gcd[m,n]∣m m n , gcd[m,n]∣n m n))

-- This could be simplified with some nice backwards/forwards reasoning
-- after the new function hierarchy is up and running.
gcd[cm,cn]/c≡gcd[m,n] : ∀ c m n .{{_ : NonZero c}} → gcd (c * m) (c * n) / c ≡ gcd m n
gcd[cm,cn]/c≡gcd[m,n] c m n = gcd-universality forwards backwards
  where
  forwards : ∀ {d : ℕ} → d ∣ m × d ∣ n → d ∣ gcd (c * m) (c * n) / c
  forwards {d} (d∣m , d∣n) = m*n∣o⇒n∣o/m c d (gcd-greatest (*-monoʳ-∣ c d∣m) (*-monoʳ-∣ c d∣n))

  backwards : ∀ {d : ℕ} → d ∣ gcd (c * m) (c * n) / c → d ∣ m × d ∣ n
  backwards {d} d∣gcd[cm,cn]/c
    with cd∣gcd[cm,n] ← m∣n/o⇒o*m∣n (gcd-greatest (m∣m*n m) (m∣m*n n)) d∣gcd[cm,cn]/c
    = *-cancelˡ-∣ c (∣-trans cd∣gcd[cm,n] (gcd[m,n]∣m (c * m) _)) ,
      *-cancelˡ-∣ c (∣-trans cd∣gcd[cm,n] (gcd[m,n]∣n (c * m) _))

c*gcd[m,n]≡gcd[cm,cn] : ∀ c m n → c * gcd m n ≡ gcd (c * m) (c * n)
c*gcd[m,n]≡gcd[cm,cn] zero      m n = ≡.sym gcd[0,0]≡0
c*gcd[m,n]≡gcd[cm,cn] c@(suc _) m n = begin
  c * gcd m n                   ≡⟨ cong (c *_) (≡.sym (gcd[cm,cn]/c≡gcd[m,n] c m n)) ⟩
  c * (gcd (c * m) (c * n) / c) ≡⟨ m*[n/m]≡n (gcd-greatest (m∣m*n m) (m∣m*n n)) ⟩
  gcd (c * m) (c * n)           ∎
  where open ≡-Reasoning

gcd[m,n]≤n : ∀ m n .{{_ : NonZero n}} → gcd m n ≤ n
gcd[m,n]≤n m n = ∣⇒≤ (gcd[m,n]∣n m n)

n/gcd[m,n]≢0 : ∀ m n .{{_ : NonZero n}} .{{gcd≢0 : NonZero (gcd m n)}} →
               n / gcd m n ≢ 0
n/gcd[m,n]≢0 m n = m<n⇒n≢0 (m≥n⇒m/n>0 {n} {gcd m n} (gcd[m,n]≤n m n))

m/gcd[m,n]≢0 : ∀ m n .{{_ : NonZero m}} .{{gcd≢0 : NonZero (gcd m n)}} →
               m / gcd m n ≢ 0
m/gcd[m,n]≢0 m n rewrite gcd-comm m n = n/gcd[m,n]≢0 n m

gcd[n,n]≡n : ∀ n → gcd n n ≡ n
gcd[n,n]≡n n = begin
  gcd n n             ≡⟨ ≡.cong₂ gcd n≢n*1 n≢n*1 ⟩
  gcd (n * 1) (n * 1) ≡⟨ ≡.sym (c*gcd[m,n]≡gcd[cm,cn] n 1 1) ⟩
  n * gcd 1 1         ≡⟨ *-identityʳ n ⟩
  n                   ∎
  where
  open ≡-Reasoning
  n≢n*1 = ≡.sym (*-identityʳ n)

------------------------------------------------------------------------
-- A formal specification of GCD

module GCD where

  -- Specification of the greatest common divisor (gcd) of two natural
  -- numbers.

  record GCD (m n gcd : ℕ) : Set where
    constructor is
    field
      -- The gcd is a common divisor.
      commonDivisor : gcd ∣ m × gcd ∣ n

      -- All common divisors divide the gcd, i.e. the gcd is the
      -- greatest common divisor according to the partial order _∣_.
      greatest : ∀ {d} → d ∣ m × d ∣ n → d ∣ gcd

    gcd∣m : gcd ∣ m
    gcd∣m = proj₁ commonDivisor

    gcd∣n : gcd ∣ n
    gcd∣n = proj₂ commonDivisor

  open GCD public


  -- The gcd is unique.

  unique : ∀ {d₁ d₂ m n} → GCD m n d₁ → GCD m n d₂ → d₁ ≡ d₂
  unique d₁ d₂ = ∣-antisym (GCD.greatest d₂ (GCD.commonDivisor d₁))
                           (GCD.greatest d₁ (GCD.commonDivisor d₂))

  -- The gcd relation is "symmetric".

  sym : ∀ {d m n} → GCD m n d → GCD n m d
  sym g = is (swap $ GCD.commonDivisor g) (GCD.greatest g ∘ swap)

  -- The gcd relation is "reflexive".

  refl : ∀ {n} → GCD n n n
  refl = is (∣-refl , ∣-refl) proj₁

  -- The GCD of 0 and n is n.

  base : ∀ {n} → GCD 0 n n
  base {n} = is (n ∣0 , ∣-refl) proj₂

  -- If d is the gcd of n and k, then it is also the gcd of n and
  -- n + k.

  step : ∀ {n k d} → GCD n k d → GCD n (n + k) d
  step {n} {k} {d} g with d₁ , d₂ ← GCD.commonDivisor g
    = is (d₁ , ∣m∣n⇒∣m+n d₁ d₂) greatest′
    where
    greatest′ : ∀ {d′} → d′ ∣ n × d′ ∣ n + k → d′ ∣ d
    greatest′ (d₁ , d₂) = GCD.greatest g (d₁ , ∣m+n∣m⇒∣n d₂ d₁)

open GCD public using (GCD) hiding (module GCD)

-- The function gcd fulfils the conditions required of GCD

gcd-GCD : ∀ m n → GCD m n (gcd m n)
gcd-GCD m n = record
  { commonDivisor = gcd[m,n]∣m m n , gcd[m,n]∣n m n
  ; greatest      = uncurry′ gcd-greatest
  }

-- Calculates the gcd of the arguments.

mkGCD : ∀ m n → ∃ λ d → GCD m n d
mkGCD m n = gcd m n , gcd-GCD m n

-- gcd as a proposition is decidable

gcd? : (m n d : ℕ) → Dec (GCD m n d)
gcd? m n d =
  Dec.map′ (λ { ≡.refl → gcd-GCD m n }) (GCD.unique (gcd-GCD m n))
           (gcd m n ≟ d)

GCD-* : ∀ {m n d c} .{{_ : NonZero c}} → GCD (m * c) (n * c) (d * c) → GCD m n d
GCD-* {c = suc _} (GCD.is (dc∣nc , dc∣mc) dc-greatest) =
  GCD.is (*-cancelʳ-∣ _ dc∣nc , *-cancelʳ-∣ _ dc∣mc)
  λ {_} → *-cancelʳ-∣ _ ∘ dc-greatest ∘ map (*-monoˡ-∣ _) (*-monoˡ-∣ _)

GCD-/ : ∀ {m n d c} .{{_ : NonZero c}} → c ∣ m → c ∣ n → c ∣ d →
        GCD m n d → GCD (m / c) (n / c) (d / c)
GCD-/ {m} {n} {d} {c} {{x}}
  (divides-refl p) (divides-refl q) (divides-refl r) gcd
  rewrite m*n/n≡m p c {{x}} | m*n/n≡m q c {{x}} | m*n/n≡m r c {{x}} = GCD-* gcd

GCD-/gcd : ∀ m n .{{_ : NonZero (gcd m n)}} → GCD (m / gcd m n) (n / gcd m n) 1
GCD-/gcd m n rewrite ≡.sym (n/n≡1 (gcd m n)) =
  GCD-/ (gcd[m,n]∣m m n) (gcd[m,n]∣n m n) ∣-refl (gcd-GCD m n)

------------------------------------------------------------------------
-- Calculating the gcd

-- The calculation also proves Bézout's lemma.

module Bézout where

  module Identity where

    -- If m and n have greatest common divisor d, then one of the
    -- following two equations is satisfied, for some numbers x and y.
    -- The proof is "lemma" below (Bézout's lemma).
    --
    -- (If this identity was stated using integers instead of natural
    -- numbers, then it would not be necessary to have two equations.)

    data Identity (d m n : ℕ) : Set where
      +- : (x y : ℕ) (eq : d + y * n ≡ x * m) → Identity d m n
      -+ : (x y : ℕ) (eq : d + x * m ≡ y * n) → Identity d m n

    -- Various properties about Identity.

    sym : ∀ {d} → Symmetric (Identity d)
    sym (+- x y eq) = -+ y x eq
    sym (-+ x y eq) = +- y x eq

    refl : ∀ {d} → Identity d d d
    refl = -+ 0 1 ≡.refl

    base : ∀ {d} → Identity d 0 d
    base = -+ 0 1 ≡.refl

    private
      infixl 7 _⊕_

      _⊕_ : ℕ → ℕ → ℕ
      m ⊕ n = 1 + m + n

    step : ∀ {d n k} → Identity d n k → Identity d n (n + k)
    step {d} {n} (+-  x  y       eq) with compare x y
    ... | equal x     = +- (2 * x)     x       (lem₂ d x   eq)
    ... | less x i    = +- (2 * x ⊕ i) (x ⊕ i) (lem₃ d x   eq)
    ... | greater y i = +- (2 * y ⊕ i) y       (lem₄ d y n eq)
    step {d} {n} (-+  x  y       eq) with compare x y
    ... | equal x     = -+ (2 * x)     x       (lem₅ d x   eq)
    ... | less x i    = -+ (2 * x ⊕ i) (x ⊕ i) (lem₆ d x   eq)
    ... | greater y i = -+ (2 * y ⊕ i) y       (lem₇ d y n eq)

  open Identity public using (Identity; +-; -+) hiding (module Identity)

  module Lemma where

    -- This type packs up the gcd, the proof that it is a gcd, and the
    -- proof that it satisfies Bézout's identity.

    data Lemma (m n : ℕ) : Set where
      result : (d : ℕ) (g : GCD m n d) (b : Identity d m n) → Lemma m n

    -- Various properties about Lemma.

    sym : Symmetric Lemma
    sym (result d g b) = result d (GCD.sym g) (Identity.sym b)

    base : ∀ d → Lemma 0 d
    base d = result d GCD.base Identity.base

    refl : ∀ d → Lemma d d
    refl d = result d GCD.refl Identity.refl

    stepˡ : ∀ {n k} → Lemma n (suc k) → Lemma n (suc (n + k))
    stepˡ {n} {k} (result d g b) =
      subst (Lemma n) (+-suc n k) $
        result d (GCD.step g) (Identity.step b)

    stepʳ : ∀ {n k} → Lemma (suc k) n → Lemma (suc (n + k)) n
    stepʳ = sym ∘ stepˡ ∘ sym

  open Lemma public using (Lemma; result) hiding (module Lemma)

  -- Bézout's lemma proved using some variant of the extended
  -- Euclidean algorithm.

  lemma : (m n : ℕ) → Lemma m n
  lemma m n = build [ <′-recBuilder ⊗ <′-recBuilder ] P gcd″ (m , n)
    where
    P : ℕ × ℕ → Set
    P (m , n) = Lemma m n

    gcd″ : ∀ p → (<′-Rec ⊗ <′-Rec) P p → P p
    gcd″ (zero      , n)     rec = Lemma.base n
    gcd″ (m@(suc _) , zero)  rec = Lemma.sym (Lemma.base m)
    gcd″ (m′@(suc m) , n′@(suc n)) rec with compare m n
    ... | equal m     = Lemma.refl m′
    ... | less m k    = Lemma.stepˡ $ proj₁ rec (lem₁ k m)
                      -- "gcd (suc m) (suc k)"
    ... | greater n k = Lemma.stepʳ $ proj₂ rec (lem₁ k n) n′
                      -- "gcd (suc k) (suc n)"

  -- Bézout's identity can be recovered from the GCD.

  identity : ∀ {m n d} → GCD m n d → Identity d m n
  identity {m} {n} g with result d g′ b ← lemma m n rewrite GCD.unique g g′ = b

------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest common divisor
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.GCD where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Properties
open import Data.Nat.Induction
  using (Acc; acc; <′-Rec; <′-recBuilder; <-wellFounded)
open import Data.Nat.Properties using (+-suc)
open import Data.Product
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Induction using (build)
open import Induction.Lexicographic using (_⊗_; [_⊗_])
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; subst; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

-- Calculated via Euclid's algorithm. In order to show progress,
-- avoiding the initial step where the first argument may increase, it
-- is necessary to first define a version `gcd′` which assumes that the
-- first argument is strictly smaller than the second. The full `gcd`
-- function then compares the two arguments and applies `gcd′`
-- accordingly.

-- The definition is marked abstract to prevent unhelpful unfolding
-- during proofs. This isn't a problem as all it's properties are
-- derivable from the 3 core properties proved below.

abstract

  gcd′ : ∀ m n → Acc _<_ m → n < m → ℕ
  gcd′ m zero        _         _   = m
  gcd′ m n@(suc n-1) (acc rec) n<m = gcd′ n (m % n) (rec _ n<m) (a%n<n m n-1)

  gcd : ℕ → ℕ → ℕ
  gcd m n with <-cmp m n
  ... | tri< m<n _ _ = gcd′ n m (<-wellFounded n) m<n
  ... | tri≈ _ _ _   = m
  ... | tri> _ _ n<m = gcd′ m n (<-wellFounded m) n<m

------------------------------------------------------------------------
-- Core properties of gcd′

abstract

  gcd′[m,n]∣m,n : ∀ {m n} rec n<m → gcd′ m n rec n<m ∣ m × gcd′ m n rec n<m ∣ n
  gcd′[m,n]∣m,n {m} {zero}  rec       n<m = ∣-refl , m ∣0
  gcd′[m,n]∣m,n {m} {suc n} (acc rec) n<m
    with gcd′[m,n]∣m,n (rec _ n<m) (a%n<n m n)
  ... | gcd∣n , gcd∣m%n = ∣n∣m%n⇒∣m gcd∣n gcd∣m%n , gcd∣n

  gcd′-greatest : ∀ {m n c} rec n<m → c ∣ m → c ∣ n → c ∣ gcd′ m n rec n<m
  gcd′-greatest {m} {zero}  rec       n<m c∣m c∣n = c∣m
  gcd′-greatest {m} {suc n} (acc rec) n<m c∣m c∣n =
    gcd′-greatest (rec _ n<m) (a%n<n m n) c∣n (%-presˡ-∣ c∣m c∣n)

------------------------------------------------------------------------
-- Core properties of gcd

abstract

  gcd[m,n]∣m : ∀ m n → gcd m n ∣ m
  gcd[m,n]∣m m n with <-cmp m n
  ... | tri< n<m _ _ = proj₂ (gcd′[m,n]∣m,n {n} {m} _ _)
  ... | tri≈ _ _ _   = ∣-refl
  ... | tri> _ _ m<n = proj₁ (gcd′[m,n]∣m,n {m} {n} _ _)

  gcd[m,n]∣n : ∀ m n → gcd m n ∣ n
  gcd[m,n]∣n m n with <-cmp m n
  ... | tri< n<m _    _ = proj₁ (gcd′[m,n]∣m,n {n} {m} _ _)
  ... | tri≈ _ P.refl _ = ∣-refl
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

gcd-comm : ∀ m n → gcd m n ≡ gcd n m
gcd-comm m n = ∣-antisym
  (gcd-greatest (gcd[m,n]∣n m n) (gcd[m,n]∣m m n))
  (gcd-greatest (gcd[m,n]∣n n m) (gcd[m,n]∣m n m))

gcd-universality : ∀ {m n g} →
                   (∀ {d} → d ∣ m × d ∣ n → d ∣ g) →
                   (∀ {d} → d ∣ g → d ∣ m × d ∣ n) →
                   g ≡ gcd m n
gcd-universality {m} {n} forwards backwards with backwards ∣-refl
... | back₁ , back₂ = ∣-antisym
  (gcd-greatest back₁ back₂)
  (forwards (gcd[m,n]∣m m n , gcd[m,n]∣n m n))

-- This could be simplified with some nice backwards/forwards reasoning
-- after the new function hierarchy is up and running.
gcd[cm,cn]/c≡gcd[m,n] : ∀ c m n {≢0} → (gcd (c * m) (c * n) / c) {≢0} ≡ gcd m n
gcd[cm,cn]/c≡gcd[m,n] c@(suc c-1) m n = gcd-universality forwards backwards
  where
  forwards : ∀ {d : ℕ} → d ∣ m × d ∣ n → d ∣ gcd (c * m) (c * n) / c
  forwards {d} (d∣m , d∣n) = m*n∣o⇒n∣o/m c d (gcd-greatest (*-monoʳ-∣ c d∣m) (*-monoʳ-∣ c d∣n))

  backwards : ∀ {d : ℕ} → d ∣ gcd (c * m) (c * n) / c → d ∣ m × d ∣ n
  backwards {d} d∣gcd[cm,cn]/c with m∣n/o⇒o*m∣n (gcd-greatest (m∣m*n m) (m∣m*n n)) d∣gcd[cm,cn]/c
  ... | cd∣gcd[cm,n] =
    *-cancelˡ-∣ c-1 (∣-trans cd∣gcd[cm,n] (gcd[m,n]∣m (c * m) (c * n))) ,
    *-cancelˡ-∣ c-1 (∣-trans cd∣gcd[cm,n] (gcd[m,n]∣n (c * m) (c * n)))

c*gcd[m,n]≡gcd[cm,cn] : ∀ c m n → c * gcd m n ≡ gcd (c * m) (c * n)
c*gcd[m,n]≡gcd[cm,cn] zero        m n = P.sym gcd[0,0]≡0
c*gcd[m,n]≡gcd[cm,cn] c@(suc c-1) m n = begin
  c * gcd m n                   ≡⟨ cong (c *_) (P.sym (gcd[cm,cn]/c≡gcd[m,n] c m n)) ⟩
  c * (gcd (c * m) (c * n) / c) ≡⟨ m*[n/m]≡n (gcd-greatest (m∣m*n m) (m∣m*n n)) ⟩
  gcd (c * m) (c * n)           ∎
  where open P.≡-Reasoning

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
  step g with GCD.commonDivisor g
  step {n} {k} {d} g | (d₁ , d₂) = is (d₁ , ∣m∣n⇒∣m+n d₁ d₂) greatest′
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
gcd? m n d with gcd m n ≟ d
... | yes P.refl = yes (gcd-GCD m n)
... | no  gcd≢d  = no (gcd≢d ∘ GCD.unique (gcd-GCD m n))

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
    refl = -+ 0 1 P.refl

    base : ∀ {d} → Identity d 0 d
    base = -+ 0 1 P.refl

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
    gcd″ (zero  , n                 ) rec = Lemma.base n
    gcd″ (suc m , zero              ) rec = Lemma.sym (Lemma.base (suc m))
    gcd″ (suc m , suc n             ) rec with compare m n
    ... | equal .m     = Lemma.refl (suc m)
    ... | less .m k    = Lemma.stepˡ $ proj₁ rec (suc k) (lem₁ k m)
                      -- "gcd (suc m) (suc k)"
    ... | greater .n k = Lemma.stepʳ $ proj₂ rec (suc k) (lem₁ k n) (suc n)
                      -- "gcd (suc k) (suc n)"

  -- Bézout's identity can be recovered from the GCD.

  identity : ∀ {m n d} → GCD m n d → Identity d m n
  identity {m} {n} g with lemma m n
  ... | result d g′ b with GCD.unique g g′
  ...   | P.refl = b

------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.GCD using (module GCD; module Bézout)
open import Data.Nat.Properties
open import Data.Product.Base using (_×_; map₂; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (flip; _∘_; _∘′_)
open import Relation.Nullary.Decidable as Dec
  using (yes; no; from-yes; from-no; ¬?; _×-dec_; _⊎-dec_; _→-dec_; decidable-stable)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable; IUniversal; Satisfiable; _∩_; _⇒_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

private
  variable
    d k m n p : ℕ

  instance
    nt[2] : NonTrivial 2
    nt[2] = nonTrivial {0}

------------------------------------------------------------------------
-- Definitions

-- Definition of having a non-trivial divisor below a given bound

record HasBoundedNonTrivialDivisor (k n : ℕ) : Set where
  constructor hasBoundedNonTrivialDivisor
  field
    {divisor} : ℕ
    .{{nt}} : NonTrivial divisor
    d<k     : divisor < k
    d∣n     : divisor ∣ n

-- smart constructors

hasBoundedNonTrivialDivisor≢ : .{{NonTrivial d}} → .{{NonZero n}} →
                    d ≢ n → d ∣ n → HasBoundedNonTrivialDivisor n n
hasBoundedNonTrivialDivisor≢ d≢n d∣n = hasBoundedNonTrivialDivisor (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

hasBoundedNonTrivialDivisor>1 : 1 < d → d < n → d ∣ n → HasBoundedNonTrivialDivisor n n
hasBoundedNonTrivialDivisor>1 1<d = hasBoundedNonTrivialDivisor
  where instance _ = n>1⇒nonTrivial 1<d

hasBoundedNonTrivialDivisor∣ : HasBoundedNonTrivialDivisor k m → m ∣ n →
                               HasBoundedNonTrivialDivisor k n
hasBoundedNonTrivialDivisor∣ (hasBoundedNonTrivialDivisor d<k d∣m) m∣n
  = hasBoundedNonTrivialDivisor d<k (∣-trans d∣m m∣n)

-- Definition of compositeness

Composite : Pred ℕ _
Composite n = HasBoundedNonTrivialDivisor n n

-- bounded equivalent
CompositeUpTo : Pred ℕ _
CompositeUpTo n = ∃⟨ (_< n) ∩ HasNonTrivialDivisor ⟩
  where
  HasNonTrivialDivisor : Pred ℕ _
  HasNonTrivialDivisor d = NonTrivial d × d ∣ n

-- smart constructors

composite : .{{NonTrivial d}} → d < n → d ∣ n → Composite n
composite {d = d} = hasBoundedNonTrivialDivisor {divisor = d}

composite≢ : ∀ d → .{{NonTrivial d}} → .{{NonZero n}} → d ≢ n → d ∣ n → Composite n
composite≢ d d≢n d∣n = hasBoundedNonTrivialDivisor≢ {d} d≢n d∣n

composite∣ : .{{NonZero n}} → Composite m → m ∣ n → Composite n
composite∣ (hasBoundedNonTrivialDivisor {d} d<k d∣n) m∣n@(divides-refl q)
  = hasBoundedNonTrivialDivisor (*-monoʳ-< q d<k) (*-monoʳ-∣ q d∣n)
  where instance
    _ = m≢0∧n>1⇒m*n>1 q d
    _ = m*n≢0⇒m≢0 q

-- Definition of 'rough': a number is k-rough
-- if all its non-trivial factors d are bounded below by k

Rough : ℕ → Pred ℕ _
Rough k n = ¬ HasBoundedNonTrivialDivisor k n

-- Definition of primality: complement of Composite
-- Constructor `prime` takes a proof isPrime that
-- NonTrivial p is p-Rough, and thereby enforces that
-- p is a fortiori NonZero and NonUnit

record Prime (p : ℕ) : Set where
  constructor prime
  field
    .{{nt}}  : NonTrivial p
    isPrime : Rough p p

-- bounded equivalent
PrimeUpTo : Pred ℕ _
PrimeUpTo n = ∀[ (_< n) ⇒ HasNoNonTrivialDivisor ]
  where
  HasNoNonTrivialDivisor : Pred ℕ _
  HasNoNonTrivialDivisor d = NonTrivial d → d ∤ n

-- Definition of irreducibility

module _ (n : ℕ) where

  private

    Irreducible′ : Pred ℕ _
    Irreducible′ d = d ∣ n → d ≡ 1 ⊎ d ≡ n
  
  Irreducible : Set
  Irreducible = ∀[ Irreducible′ ]

  IrreducibleUpTo : Set
  IrreducibleUpTo = ∀[ (_< n) ⇒ Irreducible′ ]

------------------------------------------------------------------------
-- Basic properties of Rough

-- 1 is always rough
rough-1 : ∀ k → Rough k 1
rough-1 _ (hasBoundedNonTrivialDivisor _ d∣1) = contradiction (∣1⇒≡1 d∣1) nonTrivial⇒≢1

-- Any number is 0-, 1- and 2-rough,
-- because no non-trivial factor d can be less than 0, 1, or 2
0-rough : Rough 0 n
0-rough (hasBoundedNonTrivialDivisor () _)

1-rough : Rough 1 n
1-rough (hasBoundedNonTrivialDivisor ⦃()⦄ z<s _)

2-rough : Rough 2 n
2-rough (hasBoundedNonTrivialDivisor ⦃()⦄ (s<s z<s) _)

-- If a number n > 1 is k-rough, then k ≤ n
rough⇒≤ : .⦃ NonTrivial n ⦄ → Rough k n → k ≤ n
rough⇒≤ rough = ≮⇒≥ λ k>n → rough (hasBoundedNonTrivialDivisor k>n ∣-refl)

-- If a number n is k-rough, and k ∤ n, then n is (suc k)-rough
∤⇒rough-suc : k ∤ n → Rough k n → Rough (suc k) n
∤⇒rough-suc k∤n r (hasBoundedNonTrivialDivisor d<1+k d∣n) with m<1+n⇒m<n∨m≡n d<1+k
... | inj₁ d<k      = r (hasBoundedNonTrivialDivisor d<k d∣n)
... | inj₂ d≡k@refl = contradiction d∣n k∤n

-- If a number is k-rough, then so are all of its divisors
rough⇒∣⇒rough : Rough k m → n ∣ m → Rough k n
rough⇒∣⇒rough r n∣m hbntd = r (hasBoundedNonTrivialDivisor∣ hbntd n∣m)

------------------------------------------------------------------------
-- Corollary: relationship between roughness and primality

-- If a number n is p-rough, and p > 1 divides n, then p must be prime
rough⇒∣⇒prime : .⦃ NonTrivial p ⦄ → Rough p n → p ∣ n → Prime p
rough⇒∣⇒prime r p∣n = prime (rough⇒∣⇒rough r p∣n)

------------------------------------------------------------------------
-- Basic (counter-)examples of Composite

¬composite[0] : ¬ Composite 0
¬composite[0] composite[0] = 0-rough composite[0]

¬composite[1] : ¬ Composite 1
¬composite[1] composite[1] = 1-rough composite[1]

composite[4] : Composite 4
composite[4] = composite≢ 2 (λ()) (divides-refl 2)

composite[6] : Composite 6
composite[6] = composite≢ 3 (λ()) (divides-refl 2)


------------------------------------------------------------------------
-- Basic (counter-)examples of Prime

¬prime[0] : ¬ Prime 0
¬prime[0] ()

¬prime[1] : ¬ Prime 1
¬prime[1] ()

prime[2] : Prime 2
prime[2] = prime 2-rough

------------------------------------------------------------------------
-- Basic (counter-)examples of Irreducible

¬irreducible[0] : ¬ Irreducible 0
¬irreducible[0] irr[0] = [ (λ ()) , (λ ()) ]′ (irr[0] {2} (divides-refl 0))

irreducible[1] : Irreducible 1
irreducible[1] m|1 = inj₁ (∣1⇒≡1 m|1)

irreducible[2] : Irreducible 2
irreducible[2] {zero}  0∣2 with () ← 0∣⇒≡0 0∣2
irreducible[2] {suc _} d∣2 with ∣⇒≤ d∣2
... | z<s     = inj₁ refl
... | s<s z<s = inj₂ refl


------------------------------------------------------------------------
-- NonTrivial

composite⇒nonTrivial : Composite n → NonTrivial n
composite⇒nonTrivial {1}      = flip contradiction ¬composite[1]
composite⇒nonTrivial {2+ _} _ = _

prime⇒nonTrivial : Prime p → NonTrivial p
prime⇒nonTrivial (prime _) = recompute-nonTrivial

------------------------------------------------------------------------
-- NonZero

composite⇒nonZero : Composite n → NonZero n
composite⇒nonZero {suc _} _ = _

prime⇒nonZero : Prime p → NonZero p
prime⇒nonZero (prime _) = nonTrivial⇒nonZero

irreducible⇒nonZero : Irreducible n → NonZero n
irreducible⇒nonZero {zero} = flip contradiction ¬irreducible[0]
irreducible⇒nonZero {suc _} _ = _


------------------------------------------------------------------------
-- Decidability

compositeUpTo? : Decidable CompositeUpTo
compositeUpTo? n = anyUpTo? (λ d → nonTrivial? d ×-dec d ∣? n) n

composite? : Decidable Composite
composite? n = Dec.map′ comp-upto⇒comp comp⇒comp-upto (compositeUpTo? n)
  where
  comp-upto⇒comp : CompositeUpTo n → Composite n
  comp-upto⇒comp = λ (_ , d<n , ntd , d∣n) → hasBoundedNonTrivialDivisor ⦃ ntd ⦄ d<n d∣n

  comp⇒comp-upto : Composite n → CompositeUpTo n
  comp⇒comp-upto = λ (hasBoundedNonTrivialDivisor d<n d∣n) → _ , d<n , recompute-nonTrivial , d∣n

primeUpTo? : Decidable PrimeUpTo
primeUpTo? n = allUpTo? (λ d → nonTrivial? d →-dec ¬? (d ∣? n)) n

prime? : Decidable Prime
prime? 0        = no ¬prime[0]
prime? 1        = no ¬prime[1]
prime? n@(2+ _) = Dec.map′ prime-upto⇒prime prime⇒prime-upto (primeUpTo? n)
  where
  prime-upto⇒prime : PrimeUpTo n → Prime n
  prime-upto⇒prime upto = prime
    λ (hasBoundedNonTrivialDivisor d<n d∣n) → upto d<n recompute-nonTrivial d∣n

  prime⇒prime-upto : Prime n → PrimeUpTo n
  prime⇒prime-upto (prime p) {d} d<n ntd d∣n = p (hasBoundedNonTrivialDivisor ⦃ ntd ⦄ d<n d∣n)

irreducibleUpTo? : Decidable IrreducibleUpTo
irreducibleUpTo? n = allUpTo? (λ m → (m ∣? n) →-dec ((m ≟ 1) ⊎-dec m ≟ n)) n

irreducible? : Decidable Irreducible
irreducible? zero      = no ¬irreducible[0]
irreducible? n@(suc _) = Dec.map′ irr-upto⇒irr irr⇒irr-upto (irreducibleUpTo? n)
  where
  irr-upto⇒irr : IrreducibleUpTo n → Irreducible n
  irr-upto⇒irr irr-upto m∣n
    = [ flip irr-upto m∣n , inj₂ ]′ (m≤n⇒m<n∨m≡n (∣⇒≤ m∣n))

  irr⇒irr-upto : Irreducible n → IrreducibleUpTo n
  irr⇒irr-upto irr m<n m∣n = irr m∣n

-- Examples
--
-- Once we have the above decision procdures, then instead of constructing proofs
-- of eg Prime-ness by hand, we call the appropriate function, and use the witness
-- extraction functions `from-yes`, `from-no` to return the checked proofs

private

  -- Example: 2 is prime, but not-composite.
  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)

  2-is-not-composite : ¬ Composite 2
  2-is-not-composite = from-no (composite? 2)


  -- Example: 4 and 6 are composite, hence not-prime
  4-is-composite : Composite 4
  4-is-composite = from-yes (composite? 4)

  4-is-not-prime : ¬ Prime 4
  4-is-not-prime = from-no (prime? 4)

  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)

  6-is-not-prime : ¬ Prime 6
  6-is-not-prime = from-no (prime? 6)

------------------------------------------------------------------------
-- Relationships between compositeness, primality, and irreducibility

composite⇒¬prime : Composite n → ¬ Prime n
composite⇒¬prime composite[d] (prime p) = p composite[d]

¬composite⇒prime : .⦃ NonTrivial n ⦄ → ¬ Composite n → Prime n
¬composite⇒prime = prime

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite (prime p) = p

-- note that this has to recompute the factor!
¬prime⇒composite : .⦃ NonTrivial n ⦄ → ¬ Prime n → Composite n
¬prime⇒composite {n} ¬prime[n] =
  decidable-stable (composite? n) (¬prime[n] ∘′ ¬composite⇒prime)

prime⇒irreducible : Prime p → Irreducible p
prime⇒irreducible (prime r) {0}        0∣p
  = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ _)
  where instance _ = nonTrivial⇒nonZero
prime⇒irreducible     _     {1}        1∣p = inj₁ refl
prime⇒irreducible (prime r) {m@(2+ _)} m∣p
  = inj₂ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → r (hasBoundedNonTrivialDivisor m<p m∣p))
  where instance _ = nonTrivial⇒nonZero

irreducible⇒prime : .⦃ NonTrivial p ⦄ → Irreducible p → Prime p
irreducible⇒prime irr
  = prime λ (hasBoundedNonTrivialDivisor d<p d∣p) → [ nonTrivial⇒≢1 , (<⇒≢ d<p) ]′ (irr d∣p)

------------------------------------------------------------------------
-- Euclid's lemma

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches
-- the ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclidsLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclidsLemma m n {p} (prime prp) p∣m*n = result
  where
  open ∣-Reasoning
  instance _ = nonTrivial⇒nonZero -- for NonZero p

  p∣rmn : ∀ r → p ∣ r * m * n
  p∣rmn r = begin
    p           ∣⟨ p∣m*n ⟩
    m * n       ∣⟨ n∣m*n r ⟩
    r * (m * n) ≡⟨ *-assoc r m n ⟨
    r * m * n   ∎

  result : p ∣ m ⊎ p ∣ n
  result with Bézout.lemma m p
  -- if the GCD of m and p is zero then p must be zero, which is
  -- impossible as p is a prime
  ... | Bézout.result 0 g _ = contradiction (0∣⇒≡0 (GCD.gcd∣n g)) (≢-nonZero⁻¹ _)
  -- this should be a typechecker-rejectable case!?

  -- if the GCD of m and p is one then m and p are coprime, and we know
  -- that for some integers s and r, sm + rp = 1. We can use this fact
  -- to determine that p divides n
  ... | Bézout.result 1 _ (Bézout.+- r s 1+sp≡rm) =
    inj₂ (flip ∣m+n∣m⇒∣n (n∣m*n*o s n) (begin
      p             ∣⟨ p∣rmn r ⟩
      r * m * n     ≡⟨ cong (_* n) 1+sp≡rm ⟨
      n + s * p * n ≡⟨ +-comm n (s * p * n) ⟩
      s * p * n + n ∎))

  ... | Bézout.result 1 _ (Bézout.-+ r s 1+rm≡sp) =
    inj₂ (flip ∣m+n∣m⇒∣n (p∣rmn r) (begin
      p             ∣⟨ n∣m*n*o s n ⟩
      s * p * n     ≡⟨ cong (_* n) 1+rm≡sp ⟨
      n + r * m * n ≡⟨ +-comm n (r * m * n) ⟩
      r * m * n + n ∎))

  -- if the GCD of m and p is greater than one, then it must be p and hence p ∣ m.
  ... | Bézout.result d@(2+ _) g _ with d ≟ p
  ...   | yes d≡p@refl = inj₁ (GCD.gcd∣m g)
  ...   | no  d≢p = contradiction (hasBoundedNonTrivialDivisor≢ d≢p d∣p) prp
    where
    d∣p : d ∣ p
    d∣p = GCD.gcd∣n g

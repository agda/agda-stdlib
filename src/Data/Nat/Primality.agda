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
open import Data.Product.Base using (_×_; map₂; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (flip; _∘_; _∘′_)
open import Relation.Nullary.Decidable as Dec
  using (yes; no; from-yes; from-no; ¬?; decidable-stable; _×-dec_; _⊎-dec_; _→-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable; IUniversal; Satisfiable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

private
  variable
    d k m n p : ℕ

pattern 1<2+n {n} = s<s (z<s {n})


------------------------------------------------------------------------
-- Definitions

-- Definition of 'not rough'-ness

record BoundedCompositeAt (k n d : ℕ) : Set where
  constructor boundedComposite
  field
    1<d : 1 < d
    d<k : d < k
    d∣n : d ∣ n

open BoundedCompositeAt public

pattern boundedComposite>1 {d} d<k d∣n = boundedComposite (1<2+n {d}) d<k d∣n

-- Definition of compositeness

CompositeAt : ℕ → Pred ℕ _
CompositeAt n = BoundedCompositeAt n n

Composite : ℕ → Set
Composite n = ∃⟨ CompositeAt n ⟩

-- Definition of 'rough': a number is k-rough
-- if all its factors d > 1 are greater than or equal to k

_RoughAt_ : ℕ → ℕ → Pred ℕ _
k RoughAt n = ¬_ ∘ BoundedCompositeAt k n

_Rough_ : ℕ → ℕ → Set
k Rough n = ∀[ k RoughAt n ]

-- Definition of primality: complement of Composite

PrimeAt : ℕ → Pred ℕ _
PrimeAt n = n RoughAt n

Prime : ℕ → Set
Prime n = 1 < n × ∀[ PrimeAt n ]

-- smart constructor: prime
-- this takes a proof p that n = suc (suc _) is n-Rough
-- and thereby enforces that n is a fortiori NonZero

pattern prime {n} r = 1<2+n {n} , r

-- smart destructor

prime⁻¹ : Prime n → n Rough n
prime⁻¹ (prime r) = r

-- Definition of irreducibility

IrreducibleAt : ℕ → Pred ℕ _
IrreducibleAt n d = d ∣ n → d ≡ 1 ⊎ d ≡ n

Irreducible : ℕ → Set
Irreducible n = ∀[ IrreducibleAt n ]


------------------------------------------------------------------------
-- Basic properties of Rough

-- 1 is always rough
_rough-1 : ∀ k → k Rough 1
(_ rough-1) (boundedComposite 1<d _ d∣1) = >⇒∤ 1<d d∣1

-- Any number is 0-rough
0-rough : 0 Rough n
0-rough (boundedComposite 1<d d<0 _) with () ← d<0

-- Any number is 1-rough
1-rough : 1 Rough n
1-rough (boundedComposite 1<d d<1 _) = <-asym 1<d d<1

-- Any number is 2-rough because all factors d > 1 are greater than or equal to 2
2-rough : 2 Rough n
2-rough (boundedComposite 1<d d<2 _) with () ← ≤⇒≯ 1<d d<2

-- If a number n is k-rough, and k ∤ n, then n is (suc k)-rough
∤⇒rough-suc : k ∤ n → k Rough n → suc k Rough n
∤⇒rough-suc k∤n r (boundedComposite 1<d d<1+k d∣n) with m<1+n⇒m<n∨m≡n d<1+k
... | inj₁ d<k             = r (boundedComposite 1<d d<k d∣n)
... | inj₂ d≡k rewrite d≡k = contradiction d∣n k∤n

-- If a number is k-rough, then so are all of its divisors
rough⇒∣⇒rough : k Rough m → n ∣ m → k Rough n
rough⇒∣⇒rough r n∣m (boundedComposite 1<d d<k d∣n)
  = r (boundedComposite 1<d d<k (∣-trans d∣n n∣m))

------------------------------------------------------------------------
-- Corollary: relationship between roughness and primality

-- If a number n is p-rough, and p > 1 divides n, then p must be prime
rough⇒∣⇒prime : 1 < p → p Rough n → p ∣ n → Prime p
rough⇒∣⇒prime 1<p r p∣n = 1<p , rough⇒∣⇒rough r p∣n

------------------------------------------------------------------------
-- Basic (non-)instances of Composite

¬composite[0] : ¬ Composite 0
¬composite[0] (_ , composite[0]) = 0-rough composite[0]

¬composite[1] : ¬ Composite 1
¬composite[1] (_ , composite[1]) = 1-rough composite[1]

composite[2+k≢n≢0] : .{{NonZero n}} → let d = suc (suc k) in
  d ≢ n → d ∣ n → CompositeAt n d
composite[2+k≢n≢0] d≢n d∣n = boundedComposite>1 (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

composite[4] : Composite 4
composite[4] = 2 , composite[2+k≢n≢0] (from-no (2 ≟ 4)) (divides-refl 2)

------------------------------------------------------------------------
-- Basic (non-)instances of Prime

¬prime[0] : ¬ Prime 0
¬prime[0] (() , _)

¬prime[1] : ¬ Prime 1
¬prime[1] (s<s () , _)

prime[2] : Prime 2
prime[2] = prime 2-rough

------------------------------------------------------------------------
-- Basic (non-)instances of Irreducible

¬irreducible[0] : ¬ Irreducible 0
¬irreducible[0] irr = [ (λ ()) , (λ ()) ]′ (irr {2} (divides-refl 0))

irreducible[1] : Irreducible 1
irreducible[1] m|1 = inj₁ (∣1⇒≡1 m|1)

irreducible[2] : Irreducible 2
irreducible[2] {zero}  0∣2 with () ← 0∣⇒≡0 0∣2
irreducible[2] {suc _} d∣2 with ∣⇒≤ d∣2
... | z<s     = inj₁ refl
... | s<s z<s = inj₂ refl

------------------------------------------------------------------------
-- Decidability

composite? : Decidable Composite
composite? n = Dec.map′
  (map₂ λ (d<n , 1<d , d∣n) → boundedComposite 1<d d<n d∣n)
  (map₂ λ (boundedComposite 1<d d<n d∣n) → d<n , 1<d , d∣n)
  (anyUpTo? (λ d → 1 <? d ×-dec d ∣? n) n)

prime? : Decidable Prime
prime? 0               = no ¬prime[0]
prime? 1               = no ¬prime[1]
prime? n@(suc (suc _))
  = (yes 1<2+n) ×-dec Dec.map′
      (λ h (boundedComposite 1<d d<n d∣n) → h d<n 1<d d∣n)
      (λ h {d} d<n 1<d d∣n → h (boundedComposite 1<d d<n d∣n))
      (allUpTo? (λ d → 1 <? d →-dec ¬? (d ∣? n)) n)

irreducible? : Decidable Irreducible
irreducible? zero      = no ¬irreducible[0]
irreducible? n@(suc _) = Dec.map′ bounded-irr⇒irr irr⇒bounded-irr
  (allUpTo? (λ m → (m ∣? n) →-dec ((m ≟ 1) ⊎-dec m ≟ n)) n)
  where
  BoundedIrreducible : Pred ℕ _
  BoundedIrreducible n = ∀ {m} → m < n → m ∣ n → m ≡ 1 ⊎ m ≡ n
  bounded-irr⇒irr : BoundedIrreducible n → Irreducible n
  bounded-irr⇒irr bounded-irr m∣n
    = [ flip bounded-irr m∣n , inj₂ ]′ (m≤n⇒m<n∨m≡n (∣⇒≤ m∣n))
  irr⇒bounded-irr : Irreducible n → BoundedIrreducible n
  irr⇒bounded-irr irr m<n m∣n = irr m∣n

------------------------------------------------------------------------
-- Relationships between compositeness, primality, and irreducibility

composite⇒¬prime : Composite n → ¬ Prime n
composite⇒¬prime (d , composite[d]) (prime r) = r composite[d]

¬composite⇒prime : 1 < n → ¬ Composite n → Prime n
¬composite⇒prime 1<n ¬composite[n]
  = 1<n , λ {d} composite[d] → ¬composite[n] (d , composite[d])

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite (prime r) (d , composite[d]) = r composite[d]

-- note that this has to recompute the factor!
¬prime⇒composite : 1 < n → ¬ Prime n → Composite n
¬prime⇒composite {n} 1<n ¬prime[n] =
  decidable-stable (composite? n) (¬prime[n] ∘′ ¬composite⇒prime 1<n)

prime⇒irreducible : Prime p → Irreducible p
prime⇒irreducible (prime r) {0} 0∣p = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ _)
prime⇒irreducible  p-prime  {1} 1∣p = inj₁ refl
prime⇒irreducible (prime r) {suc (suc _)} m∣p
  = inj₂ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → r (boundedComposite>1 m<p m∣p))

irreducible⇒prime : Irreducible p → 1 < p → Prime p
irreducible⇒prime irr 1<p
  = 1<p , λ (boundedComposite 1<d d<p d∣p) → [ (>⇒≢ 1<d) , (<⇒≢ d<p) ]′ (irr d∣p)

------------------------------------------------------------------------
-- Euclid's lemma

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches
-- the ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclidsLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclidsLemma m n {p} (prime pr) p∣m*n = result
  where
  open ∣-Reasoning

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
  ... | Bézout.result 0 g _ = contradiction (0∣⇒≡0 (GCD.gcd∣n g)) λ()
  -- this should be a typechecker-rejectable case!?

  -- if the GCD of m and p is one then m and p is coprime, and we know
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
  ... | Bézout.result d@(suc (suc _)) g _ with d ≟ p
  ...   | yes d≡p rewrite d≡p = inj₁ (GCD.gcd∣m g)
  ...   | no  d≢p = contradiction d∣p λ d∣p → pr (composite[2+k≢n≢0] d≢p d∣p)
    where
    d∣p : d ∣ p
    d∣p = GCD.gcd∣n g

private

  -- Example: 2 is prime.
  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)


  -- Example: 6 is composite
  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality where

open import Data.Bool.Base using (Bool; true; false; not; T)
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

------------------------------------------------------------------------
-- Definitions for `Data.Nat.Base`

pattern 2+ n = suc (suc n)

trivial : ℕ → Bool
trivial 0      = true
trivial 1      = true
trivial (2+ _) = false

Unit NonUnit NonTrivial : Pred ℕ _
Unit       = T ∘ (_≡ᵇ 1)
NonUnit    = T ∘ not ∘ (_≡ᵇ 1)
NonTrivial = T ∘ not ∘ trivial

instance
  nonUnit[0] : NonUnit 0
  nonUnit[0] = _

  nonTrivial⇒nonUnit : .{{NonTrivial n}} → NonUnit n
  nonTrivial⇒nonUnit {n = 2+ _} = _

nonUnit⇒≢1 : .{{NonUnit n}} → n ≢ 1
nonUnit⇒≢1 ⦃()⦄ refl
instance
  nonTrivial : NonTrivial (2+ n)
  nonTrivial = _

nonTrivial⇒≢1 : .{{NonTrivial n}} → n ≢ 1
nonTrivial⇒≢1 ⦃()⦄ refl

nonTrivial⇒nonZero : .{{NonTrivial n}} → NonZero n
nonTrivial⇒nonZero {n = 2+ k} = _

pattern 1<2+n {n} = s<s (z<s {n})

nonTrivial⇒n>1 : .{{NonTrivial n}} → 1 < n
nonTrivial⇒n>1 {n = 2+ _} = 1<2+n

n>1⇒nonTrivial : 1 < n → NonTrivial n
n>1⇒nonTrivial 1<2+n = _


------------------------------------------------------------------------
-- Definitions

-- Definition of having a non-trivial divisor below a given bound

record BoundedComposite (k n d : ℕ) : Set where
  constructor boundedComposite
  field
    {{nt}} : NonTrivial d
    d<k : d < k
    d∣n : d ∣ n

-- smart constructor

boundedComposite≢ : .{{NonZero n}} → {{NonTrivial d}} →
                    d ≢ n → d ∣ n → BoundedComposite n n d
boundedComposite≢ d≢n d∣n = boundedComposite (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

-- Definition of compositeness

Composite : Pred ℕ _
Composite n = ∃⟨ BoundedComposite n n ⟩

-- smart constructor

composite : .{{NonZero n}} → {{NonTrivial d}} →
            d ≢ n → d ∣ n → Composite n
composite {d = d} d≢n d∣n = d , boundedComposite≢ d≢n d∣n

-- Definition of 'rough': a number is k-rough
-- if all its non-trivial factors d 1 are greater than or equal to k

Rough : ℕ → Pred ℕ _
Rough k n = ∀[  ¬_ ∘ BoundedComposite k n ]

-- Definition of primality: complement of Composite
-- Constructor `prime` takes a proof isPrime that
-- NonTrivial p is p-Rough, and thereby enforces that
-- p is a fortiori NonZero and NonUnit

record Prime (p : ℕ) : Set where
  constructor prime
  field
    {{nt}}  : NonTrivial p
    isPrime : Rough p p

-- Definition of irreducibility

Irreducible : Pred ℕ _
Irreducible n = ∀[ irreducible n ]
  where
  irreducible : ℕ → Pred ℕ _
  irreducible n d = d ∣ n → d ≡ 1 ⊎ d ≡ n


------------------------------------------------------------------------
-- Basic properties of Rough

-- 1 is always rough
rough-1 : ∀ k → Rough k 1
rough-1 _ {2+ _} (boundedComposite _ d∣1@(divides q@(suc _) ()))

-- Any number is 0-, 1- and 2-rough,
-- because no non-trivial factor d can be less than 0, 1, or 2
0-rough : Rough 0 n
0-rough (boundedComposite () _)

1-rough : Rough 1 n
1-rough (boundedComposite ⦃()⦄ z<s _)

2-rough : Rough 2 n
2-rough (boundedComposite ⦃()⦄ (s<s z<s) _)

-- If a number n is k-rough, and k ∤ n, then n is (suc k)-rough
∤⇒rough-suc : k ∤ n → Rough k n → Rough (suc k) n
∤⇒rough-suc k∤n r (boundedComposite d<1+k d∣n) with m<1+n⇒m<n∨m≡n d<1+k
... | inj₁ d<k      = r (boundedComposite d<k d∣n)
... | inj₂ d≡k@refl = contradiction d∣n k∤n

-- If a number is k-rough, then so are all of its divisors
rough⇒∣⇒rough : Rough k m → n ∣ m → Rough k n
rough⇒∣⇒rough r n∣m (boundedComposite d<k d∣n)
  = r (boundedComposite d<k (∣-trans d∣n n∣m))

------------------------------------------------------------------------
-- Corollary: relationship between roughness and primality

-- If a number n is p-rough, and p > 1 divides n, then p must be prime
rough⇒∣⇒prime : ⦃ NonTrivial p ⦄ → Rough p n → p ∣ n → Prime p
rough⇒∣⇒prime r p∣n = prime (rough⇒∣⇒rough r p∣n)

------------------------------------------------------------------------
-- Basic (non-)instances of Composite

¬composite[0] : ¬ Composite 0
¬composite[0] (_ , composite[0]) = 0-rough composite[0]

¬composite[1] : ¬ Composite 1
¬composite[1] (_ , composite[1]) = 1-rough composite[1]

composite[4] : Composite 4
composite[4] = composite {d = 2} (λ ()) (divides 2 refl)

------------------------------------------------------------------------
-- Basic (non-)instances of Prime

¬prime[0] : ¬ Prime 0
¬prime[0] ()

¬prime[1] : ¬ Prime 1
¬prime[1] ()

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
-- NonZero

composite⇒nonZero : Composite n → NonZero n
composite⇒nonZero {n@(suc _)} _ = _

prime⇒nonZero : Prime p → NonZero p
prime⇒nonZero (prime _) = nonTrivial⇒nonZero

------------------------------------------------------------------------
-- Decidability

composite? : Decidable Composite
composite? n = Dec.map′
  (map₂ λ (d<n , 1<d , d∣n) → boundedComposite ⦃ n>1⇒nonTrivial 1<d ⦄ d<n d∣n)
  (map₂ λ (boundedComposite d<n d∣n) → d<n , nonTrivial⇒n>1 , d∣n)
  (anyUpTo? (λ d → 1 <? d ×-dec d ∣? n) n)

prime? : Decidable Prime
prime? 0       = no ¬prime[0]
prime? 1       = no ¬prime[1]
prime? n@(2+ _) = Dec.map′
  (λ r → prime λ (boundedComposite d<n d∣n) → r d<n nonTrivial⇒n>1 d∣n)
  (λ (prime p) {d} d<n 1<d d∣n → p {d} (boundedComposite ⦃ n>1⇒nonTrivial 1<d ⦄  d<n d∣n))
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
composite⇒¬prime (d , composite[d]) (prime p) = p composite[d]

¬composite⇒prime : ⦃ NonTrivial n ⦄ → ¬ Composite n → Prime n
¬composite⇒prime ¬composite[n] = prime
 λ {d} composite[d] → ¬composite[n] (d , composite[d])

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite (prime p) (d , composite[d]) = p composite[d]

-- note that this has to recompute the factor!
¬prime⇒composite : ⦃ NonTrivial n ⦄ → ¬ Prime n → Composite n
¬prime⇒composite {n} ¬prime[n] =
  decidable-stable (composite? n) (¬prime[n] ∘′ ¬composite⇒prime)

prime⇒irreducible : Prime p → Irreducible p
prime⇒irreducible (prime ⦃ nt ⦄ r) {0} 0∣p
  = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ _)
  where instance _ = nonTrivial⇒nonZero
prime⇒irreducible     _            {1}    1∣p = inj₁ refl
prime⇒irreducible (prime ⦃ nt ⦄ r) {m@(2+ k)} m∣p
  = inj₂ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → r (boundedComposite m<p m∣p))
  where instance _ = nonTrivial⇒nonZero

irreducible⇒prime : Irreducible p → ⦃ NonTrivial p ⦄ → Prime p
irreducible⇒prime irr ⦃ nt ⦄
  = prime λ (boundedComposite d<p d∣p) → [ nonTrivial⇒≢1 , (<⇒≢ d<p) ]′ (irr d∣p)

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
  ...   | no  d≢p = contradiction d∣p λ d∣p → pr (boundedComposite≢ d≢p d∣p)
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


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
  using (yes; no; from-yes; ¬?; decidable-stable; _×-dec_; _→-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable; IUniversal; Satisfiable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

private
  variable
    n p : ℕ


------------------------------------------------------------------------
-- Definitions

-- Definition of compositeness

CompositeAt : ℕ → Pred ℕ _
CompositeAt n d = 1 < d × d < n × d ∣ n

Composite : ℕ → Set
Composite n = ∃⟨ CompositeAt n ⟩

¬Composite[0] : ¬ Composite 0
¬Composite[0] (_ , _ , () , _)

¬Composite[1] : ¬ Composite 1
¬Composite[1] (_ , s<s _ , s<s () , _)

-- Definition of primality.

PrimeAt : ℕ → Pred ℕ _
PrimeAt n d = 1 < d → d < n → d ∤ n

Prime : ℕ → Set
Prime n = 1 < n × ∀[ PrimeAt n ]

pattern 1<2+n {n} = s<s (z<s {n})

pattern prime {n} p = 1<2+n {n} , p

-- Definition of irreducibility.

IrreducibleAt : ℕ → Pred ℕ _
IrreducibleAt n m = m ∣ n → m ≡ 1 ⊎ m ≡ n

Irreducible : ℕ → Set
Irreducible n = ∀[ IrreducibleAt n ]

------------------------------------------------------------------------
-- Basic instances of Prime

¬Prime[0] : ¬ Prime 0
¬Prime[0] (() , _)

¬Prime[1] : ¬ Prime 1
¬Prime[1] (s<s () , _)

prime-2 : Prime 2
prime-2 = prime λ 1<d d<2 d|2 → ≤⇒≯ 1<d d<2

------------------------------------------------------------------------
-- Basic instances of Irreducible

irreducible-1 : Irreducible 1
irreducible-1 m|1 = inj₁ (∣1⇒≡1 m|1)

irreducible-2 : Irreducible 2
irreducible-2 {zero}  0∣2 with () ← 0∣⇒≡0 0∣2
irreducible-2 {suc _} d∣2 with ∣⇒≤ d∣2
... | z<s     = inj₁ refl
... | s<s z<s = inj₂ refl

------------------------------------------------------------------------
-- NonZero

Prime⇒NonZero : Prime n → NonZero n
Prime⇒NonZero (prime _) = _

Composite⇒NonZero : Composite n → NonZero n
Composite⇒NonZero {suc _} _ = _

------------------------------------------------------------------------
-- Decidability

composite? : Decidable Composite
composite? 0               = no ¬Composite[0]
composite? 1               = no ¬Composite[1]
composite? n@(suc (suc _)) = Dec.map′
  (map₂ λ { (a , b , c) → (b , a , c)})
  (map₂ λ { (a , b , c) → (b , a , c)})
  (anyUpTo? (λ d → 1 <? d ×-dec d ∣? n) n)

prime? : Decidable Prime
prime? 0               = no ¬Prime[0]
prime? 1               = no ¬Prime[1]
prime? n@(suc (suc _)) = (yes 1<2+n) ×-dec
                         (Dec.map′ (λ f {d} → flip (f {d}))
                                   (λ f {d} → flip (f {d}))
                                   (allUpTo? (λ d → 1 <? d →-dec ¬? (d ∣? n)) n))

------------------------------------------------------------------------
-- Relationships between compositeness, primality, and irreducibility

composite⇒¬prime : Composite n → ¬ Prime n
composite⇒¬prime (d , 1<d , d<n , d∣n) (prime p) = p 1<d d<n d∣n

¬composite⇒prime : 1 < n → ¬ Composite n → Prime n
¬composite⇒prime 1<n ¬n-composite
  = 1<n , λ {d} 1<d d<n d∣n → ¬n-composite (d , 1<d , d<n , d∣n)

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite (prime p) (d , 1<d , d<n , d∣n) = p 1<d d<n d∣n

-- note that this has to recompute the factor!
¬prime⇒composite : 1 < n → ¬ Prime n → Composite n
¬prime⇒composite {n} 1<n ¬n-prime =
  decidable-stable (composite? n) (¬n-prime ∘′ ¬composite⇒prime 1<n)

prime⇒irreducible : Prime p → Irreducible p
prime⇒irreducible  p-prime  {0} 0∣p = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ _ {{Prime⇒NonZero p-prime}})
prime⇒irreducible  p-prime  {1} 1∣p = inj₁ refl
prime⇒irreducible (prime p) {suc (suc _)} m∣p
  = inj₂ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → p 1<2+n m<p m∣p)

irreducible⇒prime : Irreducible p → 1 < p → Prime p
irreducible⇒prime irr 1<p = 1<p , λ 1<d d<p d∣p → [ (>⇒≢ 1<d) , (<⇒≢ d<p) ]′ (irr d∣p)

------------------------------------------------------------------------
-- Euclid's lemma

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches
-- the ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclidsLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclidsLemma m n {p} (prime p-prime) p∣m*n = result
  where
  open ∣-Reasoning

  p∣rmn : ∀ r → p ∣ r * m * n
  p∣rmn r = begin
    p           ∣⟨ p∣m*n ⟩
    m * n       ∣⟨ n∣m*n r ⟩
    r * (m * n) ≡˘⟨ *-assoc r m n ⟩
    r * m * n   ∎

  result : p ∣ m ⊎ p ∣ n
  result with Bézout.lemma m p
  -- if the GCD of m and p is zero then p must be zero, which is
  -- impossible as p is a prime
  ... | Bézout.result 0 g _ = contradiction (0∣⇒≡0 (GCD.gcd∣n g)) λ()

  -- if the GCD of m and p is one then m and p is coprime, and we know
  -- that for some integers s and r, sm + rp = 1. We can use this fact
  -- to determine that p divides n
  ... | Bézout.result 1 _ (Bézout.+- r s 1+sp≡rm) =
    inj₂ (flip ∣m+n∣m⇒∣n (n∣m*n*o s n) (begin
      p             ∣⟨ p∣rmn r ⟩
      r * m * n     ≡˘⟨ cong (_* n) 1+sp≡rm ⟩
      n + s * p * n ≡⟨ +-comm n (s * p * n) ⟩
      s * p * n + n ∎))

  ... | Bézout.result 1 _ (Bézout.-+ r s 1+rm≡sp) =
    inj₂ (flip ∣m+n∣m⇒∣n (p∣rmn r) (begin
      p             ∣⟨ n∣m*n*o s n ⟩
      s * p * n     ≡˘⟨ cong (_* n) 1+rm≡sp ⟩
      n + r * m * n ≡⟨ +-comm n (r * m * n) ⟩
      r * m * n + n ∎))

  -- if the GCD of m and p is greater than one, then it must be p and hence p ∣ m.
  ... | Bézout.result d@(suc (suc _)) g _ with d ≟ p
  ...   | yes d≡p rewrite d≡p = inj₁ (GCD.gcd∣m g)
  ...   | no  d≢p = contradiction (GCD.gcd∣n g) (p-prime 1<2+n d<p)
    where d<p = ≤∧≢⇒< (∣⇒≤ (GCD.gcd∣n g)) d≢p

private

  -- Example: 2 is prime.
  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)


  -- Example: 6 is composite
  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)


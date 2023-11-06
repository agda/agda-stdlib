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
open import Data.Product.Base using (∃-syntax; _×_; map₂; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (flip; _∘_; _∘′_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary.Decidable as Dec
  using (yes; no; from-yes; from-no; ¬?; _×-dec_; _⊎-dec_; _→-dec_; decidable-stable)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

private
  variable
    d m n o p : ℕ
  instance
    nt[2] : NonTrivial 2
    nt[2] = nonTrivial {0}

------------------------------------------------------------------------
-- Definitions

-- The definitions of `Prime` and `Composite` in this module are intended to
-- be built up as complementary pairs of `Decidable` predicates, with `Prime`
-- given *negatively* as the universal closure of the negation of `Composite`,
-- where this is given *positively* as an existential witnessing a non-trivial
-- divisor, where such quantification is proxied by an explicit `record` type.

-- For technical reasons, in order to be able to prove decidability via the
-- `all?` and `any?` combinators for *bounded* predicates on ℕ, we further
-- define the bounded counterparts to predicates `P...` as `P...UpTo` and show
-- the equivalence of the two.

-- Finally, the definitions of the predicates `Composite` and `Prime` as the
-- 'diagonal' instances of relations involving such bounds on the possible
-- non-trivial divisors leads to the following positive/existential predicate
-- as the basis for the whole development.

-- Definition of having a non-trivial divisor below a given bound

record HasBoundedNonTrivialDivisor (m n : ℕ) : Set where
  constructor hasBoundedNonTrivialDivisor
  field
    {divisor}       : ℕ
    .{{nontrivial}} : NonTrivial divisor
    divisor-<       : divisor < m
    divisor-∣       : divisor ∣ n

-- smart constructors

hasBoundedNonTrivialDivisor-≢ : .{{NonTrivial d}} → .{{NonZero n}} →
                                d ≢ n → d ∣ n →
                                HasBoundedNonTrivialDivisor n n
hasBoundedNonTrivialDivisor-≢ d≢n d∣n
  = hasBoundedNonTrivialDivisor (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

hasBoundedNonTrivialDivisor-∣ : HasBoundedNonTrivialDivisor m n → n ∣ o →
                                HasBoundedNonTrivialDivisor m o
hasBoundedNonTrivialDivisor-∣ (hasBoundedNonTrivialDivisor d<m d∣n) n∣o
  = hasBoundedNonTrivialDivisor d<m (∣-trans d∣n n∣o)

-- Definition of compositeness

Composite : Pred ℕ _
Composite n = HasBoundedNonTrivialDivisor n n

-- equivalent bounded predicate definition

private
  CompositeUpTo : Pred ℕ _
  CompositeUpTo n = ∃[ d ] d < n × NonTrivial d × d ∣ n

-- proof of equivalence

  CompositeUpTo⇔Composite : CompositeUpTo n ⇔ Composite n
  CompositeUpTo⇔Composite = mk⇔ comp-upto⇒comp comp⇒comp-upto
    where
    comp-upto⇒comp : CompositeUpTo n → Composite n
    comp-upto⇒comp (_ , d<n , ntd , d∣n) = hasBoundedNonTrivialDivisor ⦃ ntd ⦄ d<n d∣n
    comp⇒comp-upto : Composite n → CompositeUpTo n
    comp⇒comp-upto (hasBoundedNonTrivialDivisor d<n d∣n) = _ , d<n , recompute-nonTrivial , d∣n

-- smart constructors

composite : .{{NonTrivial d}} → d < n → d ∣ n → Composite n
composite {d = d} = hasBoundedNonTrivialDivisor {divisor = d}

composite-≢ : ∀ d → .{{NonTrivial d}} → .{{NonZero n}} → d ≢ n → d ∣ n → Composite n
composite-≢ d = hasBoundedNonTrivialDivisor-≢ {d}

composite-∣ : .{{NonZero n}} → Composite m → m ∣ n → Composite n
composite-∣ (hasBoundedNonTrivialDivisor {d} d<m d∣n) m∣n@(divides-refl q)
  = hasBoundedNonTrivialDivisor (*-monoʳ-< q d<m) (*-monoʳ-∣ q d∣n)
  where instance
    _ = m≢0∧n>1⇒m*n>1 q d
    _ = m*n≢0⇒m≢0 q

-- Definition of 'rough': a number is m-rough
-- if all its non-trivial divisors d are bounded below by m

Rough : ℕ → Pred ℕ _
Rough m n = ¬ HasBoundedNonTrivialDivisor m n

-- Definition of Prime as the complement of Composite, via diagonal of Rough

-- Constructor `prime` takes a proof isPrime that NonTrivial p is p-Rough
-- and thereby enforces that:
-- * p is a fortiori NonZero and NonUnit
-- * any non-trivial divisor of p must be at least p, ie p itself

record Prime (p : ℕ) : Set where
  constructor prime
  field
    .{{nontrivial}} : NonTrivial p
    isPrime         : Rough p p

-- equivalent bounded predicate definition; proof of equivalence

private
  PrimeUpTo : Pred ℕ _
  PrimeUpTo n = ∀ {d} → d < n → NonTrivial d → d ∤ n

  PrimeUpTo⇔Prime : .{{NonTrivial n}} → PrimeUpTo n ⇔ Prime n
  PrimeUpTo⇔Prime = mk⇔ prime-upto⇒prime prime⇒prime-upto
    where
    prime-upto⇒prime : .{{NonTrivial n}} → PrimeUpTo n → Prime n
    prime-upto⇒prime upto = prime
      λ (hasBoundedNonTrivialDivisor d<n d∣n) → upto d<n recompute-nonTrivial d∣n

    prime⇒prime-upto : Prime n → PrimeUpTo n
    prime⇒prime-upto (prime p) {d} d<n ntd d∣n
      = p (hasBoundedNonTrivialDivisor ⦃ ntd ⦄ d<n d∣n)

-- Definition of irreducibility: kindergarten version of `Prime`

Irreducible′ : Rel ℕ _
Irreducible′ d n = d ∣ n → d ≡ 1 ⊎ d ≡ n

Irreducible : Pred ℕ _
Irreducible n = ∀ {d} → Irreducible′ d n

-- equivalent bounded predicate definition; proof of equivalence

private
  IrreducibleUpTo : Pred ℕ _
  IrreducibleUpTo n = ∀ {d} → d < n → Irreducible′ d n

  IrreducibleUpTo⇔Irreducible : .{{NonZero n}} → IrreducibleUpTo n ⇔ Irreducible n
  IrreducibleUpTo⇔Irreducible = mk⇔ irr-upto⇒irr irr⇒irr-upto
    where
    irr-upto⇒irr : .{{NonZero n}} → IrreducibleUpTo n → Irreducible n
    irr-upto⇒irr irr-upto m∣n
      = [ flip irr-upto m∣n , inj₂ ]′ (m≤n⇒m<n∨m≡n (∣⇒≤ m∣n))

    irr⇒irr-upto : Irreducible n → IrreducibleUpTo n
    irr⇒irr-upto irr m<n m∣n = irr m∣n

------------------------------------------------------------------------
-- Basic properties of Rough

-- 1 is always rough
rough-1 : ∀ m → Rough m 1
rough-1 _ (hasBoundedNonTrivialDivisor _ d∣1) = contradiction (∣1⇒≡1 d∣1) nonTrivial⇒≢1

-- Any number is 0-, 1- and 2-rough,
-- because no non-trivial factor d can be less than 0, 1, or 2
0-rough : Rough 0 n
0-rough (hasBoundedNonTrivialDivisor () _)

1-rough : Rough 1 n
1-rough (hasBoundedNonTrivialDivisor ⦃()⦄ z<s _)

2-rough : Rough 2 n
2-rough (hasBoundedNonTrivialDivisor ⦃()⦄ (s<s z<s) _)

-- If a number n > 1 is m-rough, then m ≤ n
rough⇒≤ : .⦃ NonTrivial n ⦄ → Rough m n → m ≤ n
rough⇒≤ rough = ≮⇒≥ λ m>n → rough (hasBoundedNonTrivialDivisor m>n ∣-refl)

-- If a number n is m-rough, and m ∤ n, then n is (suc m)-rough
∤⇒rough-suc : m ∤ n → Rough m n → Rough (suc m) n
∤⇒rough-suc m∤n r (hasBoundedNonTrivialDivisor d<1+m d∣n) with m<1+n⇒m<n∨m≡n d<1+m
... | inj₁ d<m      = r (hasBoundedNonTrivialDivisor d<m d∣n)
... | inj₂ d≡m@refl = contradiction d∣n m∤n

-- If a number is m-rough, then so are all of its divisors
rough⇒∣⇒rough : Rough m o → n ∣ o → Rough m n
rough⇒∣⇒rough r n∣o hbntd = r (hasBoundedNonTrivialDivisor-∣ hbntd n∣o)

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
composite[4] = composite-≢ 2 (λ()) (divides-refl 2)

composite[6] : Composite 6
composite[6] = composite-≢ 3 (λ()) (divides-refl 2)


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
composite⇒nonTrivial {1}    composite[1] = contradiction composite[1] ¬composite[1]
composite⇒nonTrivial {2+ _} _            = _

prime⇒nonTrivial : Prime p → NonTrivial p
prime⇒nonTrivial (prime _) = recompute-nonTrivial

------------------------------------------------------------------------
-- NonZero

composite⇒nonZero : Composite n → NonZero n
composite⇒nonZero {suc _} _ = _

prime⇒nonZero : Prime p → NonZero p
prime⇒nonZero (prime _) = nonTrivial⇒nonZero

irreducible⇒nonZero : Irreducible n → NonZero n
irreducible⇒nonZero {zero}    = flip contradiction ¬irreducible[0]
irreducible⇒nonZero {suc _} _ = _


------------------------------------------------------------------------
-- Decidability

compositeUpTo? : Decidable CompositeUpTo
compositeUpTo? n = anyUpTo? (λ d → nonTrivial? d ×-dec d ∣? n) n

composite? : Decidable Composite
composite? n = Dec.map (CompositeUpTo⇔Composite {n}) (compositeUpTo? n)

primeUpTo? : Decidable PrimeUpTo
primeUpTo? n = allUpTo? (λ d → nonTrivial? d →-dec ¬? (d ∣? n)) n

prime? : Decidable Prime
prime? 0        = no ¬prime[0]
prime? 1        = no ¬prime[1]
prime? n@(2+ _) = Dec.map PrimeUpTo⇔Prime (primeUpTo? n)

irreducibleUpTo? : Decidable IrreducibleUpTo
irreducibleUpTo? n = allUpTo? (λ m → (m ∣? n) →-dec ((m ≟ 1) ⊎-dec m ≟ n)) n

irreducible? : Decidable Irreducible
irreducible? zero      = no ¬irreducible[0]
irreducible? n@(suc _) = Dec.map (IrreducibleUpTo⇔Irreducible {n}) (irreducibleUpTo? n)

-- Examples
--
-- Once we have the above decision procedures, then instead of constructing proofs
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
prime⇒irreducible pp@(prime _) {0}        0∣p
  = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ _)
  where instance _ = prime⇒nonZero pp
prime⇒irreducible     _     {1}        1∣p = inj₁ refl
prime⇒irreducible pp@(prime pr) {m@(2+ _)} m∣p
  = inj₂ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → pr (hasBoundedNonTrivialDivisor m<p m∣p))
  where instance _ = prime⇒nonZero pp

irreducible⇒prime : .⦃ NonTrivial p ⦄ → Irreducible p → Prime p
irreducible⇒prime irr = prime
  λ (hasBoundedNonTrivialDivisor d<p d∣p) → [ nonTrivial⇒≢1 , (<⇒≢ d<p) ]′ (irr d∣p)

------------------------------------------------------------------------
-- Euclid's lemma

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches
-- the ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclidsLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclidsLemma m n {p} pp@(prime pr) p∣m*n = result
  where
  open ∣-Reasoning
  instance _ = prime⇒nonZero pp

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
  ...   | no  d≢p = contradiction (hasBoundedNonTrivialDivisor-≢ d≢p (GCD.gcd∣n g)) pr

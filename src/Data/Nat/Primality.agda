------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality where

open import Data.List.Base using ([]; _∷_; product)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
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
open import Relation.Nullary.Negation using (¬_; contradiction; contradiction₂)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong)

private
  variable
    d m n o p : ℕ

  recompute-nonTrivial : .{{NonTrivial n}} → NonTrivial n
  recompute-nonTrivial {n} {{nontrivial}} =
    Dec.recompute (nonTrivial? n) nontrivial

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- The positive/existential relation `BoundedNonTrivialDivisor` is
-- the basis for the whole development, as it captures the possible
-- non-trivial divisors of a given number; its complement, `Rough`,
-- therefore sets *lower* bounds on any possible such divisors.

-- The predicate `Composite` is then defined as the 'diagonal' instance
-- of `BoundedNonTrivialDivisor`, while `Prime` is essentially defined as
-- the complement of `Composite`. Finally, `Irreducible` is the positive
-- analogue of `Prime`.

------------------------------------------------------------------------
-- Roughness

-- A number is m-rough if all its non-trivial divisors are bounded below
-- by m.
infix 10 _Rough_

_Rough_ : ℕ → Pred ℕ _
m Rough n = ¬ (n HasNonTrivialDivisorLessThan m)

------------------------------------------------------------------------
-- Compositeness

-- A number is composite if it has a proper non-trivial divisor.
Composite : Pred ℕ _
Composite n = n HasNonTrivialDivisorLessThan n

-- A shorter pattern synonym for the record constructor producing a
-- witness for `Composite`.
pattern
  composite {d} d<n d∣n = hasNonTrivialDivisor {divisor = d} d<n d∣n

------------------------------------------------------------------------
-- Primality

-- Prime as the complement of Composite (and hence the diagonal of Rough
-- as defined above). The constructor `prime` takes a proof `notComposite`
-- that NonTrivial p is not composite and thereby enforces that:
-- * p is a fortiori NonZero and NonUnit
-- * p is p-Rough, i.e. any proper divisor must be at least p, i.e. p itself
record Prime (p : ℕ) : Set where
  constructor prime
  field
    .{{nontrivial}} : NonTrivial p
    notComposite    : ¬ Composite p

------------------------------------------------------------------------
-- Irreducibility

Irreducible : Pred ℕ _
Irreducible n = ∀ {d} → d ∣ n → d ≡ 1 ⊎ d ≡ n

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Roughness

-- 1 is always n-rough
rough-1 : ∀ n → n Rough 1
rough-1 _ (hasNonTrivialDivisor _ d∣1) =
  contradiction (∣1⇒≡1 d∣1) nonTrivial⇒≢1

-- Any number is 0-, 1- and 2-rough,
-- because no proper divisor d can be strictly less than 0, 1, or 2
0-rough : 0 Rough n
0-rough (hasNonTrivialDivisor () _)

1-rough : 1 Rough n
1-rough (hasNonTrivialDivisor {{()}} z<s _)

2-rough : 2 Rough n
2-rough (hasNonTrivialDivisor {{()}} (s<s z<s) _)

-- If a number n > 1 is m-rough, then m ≤ n
rough⇒≤ : .{{NonTrivial n}} → m Rough n → m ≤ n
rough⇒≤ rough = ≮⇒≥ n≮m
  where n≮m = λ m>n → rough (hasNonTrivialDivisor m>n ∣-refl)

-- If a number n is m-rough, and m ∤ n, then n is (suc m)-rough
∤⇒rough-suc : m ∤ n → m Rough n → (suc m) Rough n
∤⇒rough-suc m∤n r (hasNonTrivialDivisor d<1+m d∣n)
  with m<1+n⇒m<n∨m≡n d<1+m
... | inj₁ d<m      = r (hasNonTrivialDivisor d<m d∣n)
... | inj₂ d≡m@refl = contradiction d∣n m∤n

-- If a number is m-rough, then so are all of its divisors
rough∧∣⇒rough : m Rough o → n ∣ o → m Rough n
rough∧∣⇒rough r n∣o bntd = r (hasNonTrivialDivisor-∣ bntd n∣o)

------------------------------------------------------------------------
-- Compositeness

-- Smart constructors

composite-≢ : ∀ d → .{{NonTrivial d}} → .{{NonZero n}} →
              d ≢ n → d ∣ n → Composite n
composite-≢ d = hasNonTrivialDivisor-≢ {d}

composite-∣ : .{{NonZero n}} → Composite m → m ∣ n → Composite n
composite-∣ (composite {d} d<m d∣n) m∣n@(divides-refl q)
  = composite (*-monoʳ-< q d<m) (*-monoʳ-∣ q d∣n)
  where instance
    _ = m≢0∧n>1⇒m*n>1 q d
    _ = m*n≢0⇒m≢0 q

-- Basic (counter-)examples of Composite

¬composite[0] : ¬ Composite 0
¬composite[0] = 0-rough

¬composite[1] : ¬ Composite 1
¬composite[1] = 1-rough

composite[4] : Composite 4
composite[4] = composite-≢ 2 (λ()) (divides-refl 2)

composite[6] : Composite 6
composite[6] = composite-≢ 3 (λ()) (divides-refl 2)

composite⇒nonZero : Composite n → NonZero n
composite⇒nonZero {suc _} _ = _

composite⇒nonTrivial : Composite n → NonTrivial n
composite⇒nonTrivial {1}    composite[1] =
  contradiction composite[1] ¬composite[1]
composite⇒nonTrivial {2+ _} _            = _

composite? : Decidable Composite
composite? n = Dec.map CompositeUpTo⇔Composite (compositeUpTo? n)
  where
  -- For technical reasons, in order to be able to prove decidability
  -- via the `all?` and `any?` combinators for *bounded* predicates on
  -- `ℕ`, we further define the bounded counterparts to predicates
  -- `P...` as `P...UpTo` and show the equivalence of the two.

  -- Equivalent bounded predicate definition
  CompositeUpTo : Pred ℕ _
  CompositeUpTo n = ∃[ d ] d < n × NonTrivial d × d ∣ n

  -- Proof of equivalence
  comp-upto⇒comp : CompositeUpTo n → Composite n
  comp-upto⇒comp (_ , d<n , ntd , d∣n) = composite d<n d∣n
    where instance _ = ntd

  comp⇒comp-upto : Composite n → CompositeUpTo n
  comp⇒comp-upto (composite d<n d∣n) = _ , d<n , recompute-nonTrivial , d∣n

  CompositeUpTo⇔Composite : CompositeUpTo n ⇔ Composite n
  CompositeUpTo⇔Composite = mk⇔ comp-upto⇒comp comp⇒comp-upto

  -- Proof of decidability
  compositeUpTo? : Decidable CompositeUpTo
  compositeUpTo? n = anyUpTo? (λ d → nonTrivial? d ×-dec d ∣? n) n

------------------------------------------------------------------------
-- Primality

-- Basic (counter-)examples

¬prime[0] : ¬ Prime 0
¬prime[0] ()

¬prime[1] : ¬ Prime 1
¬prime[1] ()

prime[2] : Prime 2
prime[2] = prime 2-rough

prime⇒nonZero : Prime p → NonZero p
prime⇒nonZero _ = nonTrivial⇒nonZero _

prime⇒nonTrivial : Prime p → NonTrivial p
prime⇒nonTrivial _ = recompute-nonTrivial

prime? : Decidable Prime
prime? 0        = no ¬prime[0]
prime? 1        = no ¬prime[1]
prime? n@(2+ _) = Dec.map PrimeUpTo⇔Prime (primeUpTo? n)
  where
  -- Equivalent bounded predicate definition
  PrimeUpTo : Pred ℕ _
  PrimeUpTo n = ∀ {d} → d < n → NonTrivial d → d ∤ n

  -- Proof of equivalence
  prime⇒prime-upto : Prime n → PrimeUpTo n
  prime⇒prime-upto (prime p) {d} d<n ntd d∣n
    = p (composite d<n d∣n) where instance _ = ntd

  prime-upto⇒prime : .{{NonTrivial n}} → PrimeUpTo n → Prime n
  prime-upto⇒prime upto = prime
    λ (composite d<n d∣n) → upto d<n recompute-nonTrivial d∣n

  PrimeUpTo⇔Prime : .{{NonTrivial n}} → PrimeUpTo n ⇔ Prime n
  PrimeUpTo⇔Prime = mk⇔ prime-upto⇒prime prime⇒prime-upto

  -- Proof of decidability
  primeUpTo? : Decidable PrimeUpTo
  primeUpTo? n = allUpTo? (λ d → nonTrivial? d →-dec ¬? (d ∣? n)) n

-- Euclid's lemma - for p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
--
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
  -- impossible as p is a prime.
  -- note: this should be a typechecker-rejectable case!?
  ... | Bézout.result 0 g _ =
    contradiction (0∣⇒≡0 (GCD.gcd∣n g)) (≢-nonZero⁻¹ _)

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

  -- if the GCD of m and p is greater than one, then it must be p and
  -- hence p ∣ m.
  ... | Bézout.result d@(2+ _) g _ with d ≟ p
  ...   | yes d≡p@refl = inj₁ (GCD.gcd∣m g)
  ...   | no  d≢p = contradiction (composite-≢ d d≢p (GCD.gcd∣n g)) pr

-- Relationship between roughness and primality.
prime⇒rough : Prime p → p Rough p
prime⇒rough (prime pr) = pr

-- If a number n is p-rough, and p > 1 divides n, then p must be prime
rough∧∣⇒prime : .{{NonTrivial p}} → p Rough n → p ∣ n → Prime p
rough∧∣⇒prime r p∣n = prime (rough∧∣⇒rough r p∣n)

-- If a number n is m-rough, and m * m > n, then n must be prime.
rough∧square>⇒prime : .{{NonTrivial n}} → m Rough n → m * m > n → Prime n
rough∧square>⇒prime rough m*m>n = prime ¬composite
  where
    ¬composite : ¬ Composite _
    ¬composite (composite d<n d∣n) = contradiction (m∣n⇒n≡quotient*m d∣n)
      (<⇒≢ (<-≤-trans m*m>n (*-mono-≤
        (rough⇒≤ (rough∧∣⇒rough rough (quotient-∣ d∣n)))
        (rough⇒≤ (rough∧∣⇒rough rough d∣n)))))
      where instance _ = n>1⇒nonTrivial (quotient>1 d∣n d<n)

-- Relationship between compositeness and primality.
composite⇒¬prime : Composite n → ¬ Prime n
composite⇒¬prime composite[d] (prime p) = p composite[d]

¬composite⇒prime : .{{NonTrivial n}} → ¬ Composite n → Prime n
¬composite⇒prime = prime

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite (prime p) = p

-- Note that this has to recompute the factor!
¬prime⇒composite : .{{NonTrivial n}} → ¬ Prime n → Composite n
¬prime⇒composite {n} ¬prime[n] =
  decidable-stable (composite? n) (¬prime[n] ∘′ ¬composite⇒prime)

productOfPrimes≢0 : ∀ {as} → All Prime as → NonZero (product as)
productOfPrimes≢0 pas = product≢0 (All.map prime⇒nonZero pas)
  where
  product≢0 : ∀ {ns} → All NonZero ns → NonZero (product ns)
  product≢0 [] = _
  product≢0 {n ∷ ns} (nzn ∷ nzns) = m*n≢0 n _ {{nzn}} {{product≢0 nzns}}

productOfPrimes≥1 : ∀ {as} → All Prime as → product as ≥ 1
productOfPrimes≥1 {as} pas = >-nonZero⁻¹ _ {{productOfPrimes≢0 pas}}

------------------------------------------------------------------------
-- Basic (counter-)examples of Irreducible

¬irreducible[0] : ¬ Irreducible 0
¬irreducible[0] irr[0] = contradiction₂ 2≡1⊎2≡0 (λ ()) (λ ())
  where 2≡1⊎2≡0 = irr[0] {2} (divides-refl 0)

irreducible[1] : Irreducible 1
irreducible[1] m∣1 = inj₁ (∣1⇒≡1 m∣1)

irreducible[2] : Irreducible 2
irreducible[2] {zero}  0∣2 with () ← 0∣⇒≡0 0∣2
irreducible[2] {suc _} d∣2 with ∣⇒≤ d∣2
... | z<s     = inj₁ refl
... | s<s z<s = inj₂ refl

irreducible⇒nonZero : Irreducible n → NonZero n
irreducible⇒nonZero {zero}    = flip contradiction ¬irreducible[0]
irreducible⇒nonZero {suc _} _ = _

irreducible? : Decidable Irreducible
irreducible? zero      = no ¬irreducible[0]
irreducible? n@(suc _) =
  Dec.map IrreducibleUpTo⇔Irreducible (irreducibleUpTo? n)
  where
  -- Equivalent bounded predicate definition
  IrreducibleUpTo : Pred ℕ _
  IrreducibleUpTo n = ∀ {d} → d < n → d ∣ n → d ≡ 1 ⊎ d ≡ n

  -- Proof of equivalence
  irr-upto⇒irr : .{{NonZero n}} → IrreducibleUpTo n → Irreducible n
  irr-upto⇒irr irr-upto m∣n
    = [ flip irr-upto m∣n , inj₂ ]′ (m≤n⇒m<n∨m≡n (∣⇒≤ m∣n))

  irr⇒irr-upto : Irreducible n → IrreducibleUpTo n
  irr⇒irr-upto irr m<n m∣n = irr m∣n

  IrreducibleUpTo⇔Irreducible : .{{NonZero n}} →
                                 IrreducibleUpTo n ⇔ Irreducible n
  IrreducibleUpTo⇔Irreducible = mk⇔ irr-upto⇒irr irr⇒irr-upto

  -- Decidability
  irreducibleUpTo? : Decidable IrreducibleUpTo
  irreducibleUpTo? n = allUpTo?
    (λ m → (m ∣? n) →-dec (m ≟ 1 ⊎-dec m ≟ n)) n

-- Relationship between primality and irreducibility.
prime⇒irreducible : Prime p → Irreducible p
prime⇒irreducible {p} pp@(prime pr) = irr
  where
  instance _ = prime⇒nonZero pp
  irr : .{{NonZero p}} → Irreducible p
  irr {0}    0∣p = contradiction (0∣⇒≡0 0∣p) (≢-nonZero⁻¹ p)
  irr {1}    1∣p = inj₁ refl
  irr {2+ _} d∣p = inj₂ (≤∧≮⇒≡ (∣⇒≤ d∣p) d≮p)
    where d≮p = λ d<p → pr (composite d<p d∣p)


irreducible⇒prime : .{{NonTrivial p}} → Irreducible p → Prime p
irreducible⇒prime irr = prime
  λ (composite d<p d∣p) → [ nonTrivial⇒≢1 , (<⇒≢ d<p) ]′ (irr d∣p)

------------------------------------------------------------------------
-- Using decidability

-- Once we have the above decision procedures, then instead of
-- constructing proofs of e.g. Prime-ness by hand, we call the
-- appropriate function, and use the witness extraction functions
-- `from-yes`, `from-no` to return the checked proofs.

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

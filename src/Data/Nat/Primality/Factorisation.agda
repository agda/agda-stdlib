------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorisation of natural numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorisation where

open import Data.Nat.Base
open import Data.Nat.Divisibility
  using (_∣?_; quotient; quotient>1; quotient-<; quotient-∣; m∣n⇒n≡m*quotient; _∣_; ∣1⇒≡1;
        divides)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-Rec; <-rec; <-recBuilder)
open import Data.Nat.Primality
  using (Prime; _Rough_; rough∧square>⇒prime; ∤⇒rough-suc; rough∧∣⇒rough; rough∧∣⇒prime;
         2-rough; euclidsLemma; prime⇒irreducible; ¬prime[1]; productOfPrimes≥1; prime⇒nonZero)
open import Data.Product.Base using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; _++_; product)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; prep; swap; ↭-reflexive; ↭-refl; ↭-trans; refl; module PermutationReasoning)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (product-↭; All-resp-↭; shift)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_$_; _∘_; _|>_; flip)
open import Induction using (build)
open import Induction.Lexicographic using (_⊗_; [_⊗_])
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Core definition

record PrimeFactorisation (n : ℕ) : Set where
  field
    factors : List ℕ
    isFactorisation : n ≡ product factors
    factorsPrime : All Prime factors

open PrimeFactorisation public using (factors)
open PrimeFactorisation

------------------------------------------------------------------------
-- Finding a factorisation

primeFactorisation[1] : PrimeFactorisation 1
primeFactorisation[1] = record
  { factors = []
  ; isFactorisation = refl
  ; factorsPrime = []
  }

primeFactorisation[p] : Prime n → PrimeFactorisation n
primeFactorisation[p] {n} pr = record
  { factors = n ∷ []
  ; isFactorisation = sym (*-identityʳ n)
  ; factorsPrime = pr ∷ []
  }

-- This builds up three important things:
-- * a proof that every number we've gotten to so far has increasingly higher
--   possible least prime factor, so we don't have to repeat smaller factors
--   over and over (this is the "m" and "rough" parameters)
-- * a witness that this limit is getting closer to the number of interest, in a
--   way that helps the termination checker (the "k" and "eq" parameters)
-- * a proof that we can factorise any smaller number, which is useful when we
--   encounter a factor, as we can then divide by that factor and continue from
--   there without termination issues
factorise : ∀ n → .{{NonZero n}} → PrimeFactorisation n
factorise 1 = primeFactorisation[1]
factorise n₀@(2+ _) = build [ <-recBuilder ⊗ <-recBuilder ] P facRec (n₀ , suc n₀ ∸ 4) 2-rough refl
  where
  P : ℕ × ℕ → Set
  P (n , k) = ∀ {m} → .{{NonTrivial n}} → .{{NonTrivial m}} → m Rough n → suc n ∸ m * m ≡ k → PrimeFactorisation n

  facRec : ∀ n×k → (<-Rec ⊗ <-Rec) P n×k → P n×k
  facRec (n , zero) _ rough eq =
  -- Case 1: m * m > n, ∴ Prime n
    primeFactorisation[p] (rough∧square>⇒prime rough (m∸n≡0⇒m≤n eq))
  facRec (n@(2+ _) , suc k) (recFactor , recQuotient) {m@(2+ _)} rough eq with m ∣? n
  -- Case 2: m ∤ n, try larger m, reducing k accordingly
  ... | no m∤n = recFactor (≤-<-trans (m∸n≤m k (m + m)) (n<1+n k)) {suc m} (∤⇒rough-suc m∤n rough) $ begin
    suc n ∸ (suc m + m * suc m)   ≡⟨ cong (λ # → suc n ∸ (suc m + #)) (*-suc m m) ⟩
    suc n ∸ (suc m + (m + m * m)) ≡⟨ cong (suc n ∸_) (+-assoc (suc m) m (m * m)) ⟨
    suc n ∸ (suc (m + m) + m * m) ≡⟨ cong (suc n ∸_) (+-comm (suc (m + m)) (m * m)) ⟩
    suc n ∸ (m * m + suc (m + m)) ≡⟨ ∸-+-assoc (suc n) (m * m) (suc (m + m)) ⟨
    (suc n ∸ m * m) ∸ suc (m + m) ≡⟨ cong (_∸ suc (m + m)) eq ⟩
    suc k ∸ suc (m + m)           ∎
    where open ≡-Reasoning
  -- Case 3: m ∣ n, record m and recurse on the quotient
  ... | yes m∣n = record
    { factors = m ∷ ps
    ; isFactorisation = sym m*Πps≡n
    ; factorsPrime = rough∧∣⇒prime rough m∣n ∷ primes
    }
    where
      m<n : m < n
      m<n = begin-strict
        m            <⟨ s≤s (≤-trans (m≤n+m m _) (+-monoʳ-≤ _ (m≤m+n m _))) ⟩
        pred (m * m) <⟨ s<s⁻¹ (m∸n≢0⇒n<m λ eq′ → 0≢1+n (trans (sym eq′) eq)) ⟩
        n            ∎
        where open ≤-Reasoning

      q = quotient m∣n

      instance _  = n>1⇒nonTrivial (quotient>1 m∣n m<n)

      factorisation[q] : PrimeFactorisation q
      factorisation[q] = recQuotient (quotient-< m∣n) (suc q ∸ m * m) (rough∧∣⇒rough rough (quotient-∣ m∣n)) refl

      ps = factors factorisation[q]

      primes = factorsPrime factorisation[q]

      m*Πps≡n : m * product ps ≡ n
      m*Πps≡n = begin
        m * product ps ≡⟨ cong (m *_) (isFactorisation factorisation[q]) ⟨
        m * q          ≡⟨ m∣n⇒n≡m*quotient m∣n ⟨
        n              ∎
        where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of a factorisation

factorisationHasAllPrimeFactors : ∀ {as} {p} → Prime p → p ∣ product as → All Prime as → p ∈ as
factorisationHasAllPrimeFactors {[]} {2+ p} pPrime p∣Πas [] = contradiction (∣1⇒≡1 p∣Πas) λ ()
factorisationHasAllPrimeFactors {a ∷ as} {p} pPrime p∣aΠas (aPrime ∷ asPrime) with euclidsLemma a (product as) pPrime p∣aΠas
... | inj₂ p∣Πas = there (factorisationHasAllPrimeFactors pPrime p∣Πas asPrime)
... | inj₁ p∣a with prime⇒irreducible aPrime p∣a
...   | inj₁ refl = contradiction pPrime ¬prime[1]
...   | inj₂ refl = here refl

private
  factorisationUnique′ : (as bs : List ℕ) → product as ≡ product bs → All Prime as → All Prime bs → as ↭ bs
  factorisationUnique′ [] [] Πas≡Πbs asPrime bsPrime = refl
  factorisationUnique′ [] (b@(2+ _) ∷ bs) Πas≡Πbs prime[as] (_ ∷ prime[bs]) =
    contradiction Πas≡Πbs (<⇒≢ Πas<Πbs)
    where
      Πas<Πbs : product [] < product (b ∷ bs)
      Πas<Πbs = begin-strict
        1                ≡⟨⟩
        1 * 1            <⟨ *-monoˡ-< 1 {1} {b} sz<ss ⟩
        b * 1            ≤⟨ *-monoʳ-≤ b (productOfPrimes≥1 prime[bs]) ⟩
        b * product bs   ≡⟨⟩
        product (b ∷ bs) ∎
        where open ≤-Reasoning

  factorisationUnique′ (a ∷ as) bs Πas≡Πbs (prime[a] ∷ prime[as]) prime[bs] = a∷as↭bs
    where
      a∣Πbs : a ∣ product bs
      a∣Πbs = divides (product as) $ begin
        product bs       ≡⟨ Πas≡Πbs ⟨
        product (a ∷ as) ≡⟨⟩
        a * product as   ≡⟨ *-comm a (product as) ⟩
        product as * a   ∎
        where open ≡-Reasoning

      shuffle : ∃[ bs′ ] bs ↭ a ∷ bs′
      shuffle with ys , zs , p ← ∈-∃++ (factorisationHasAllPrimeFactors prime[a] a∣Πbs prime[bs])
        = ys ++ zs , ↭-trans (↭-reflexive p) (shift a ys zs)

      bs′ = proj₁ shuffle
      bs↭a∷bs′ = proj₂ shuffle

      Πas≡Πbs′ : product as ≡ product bs′
      Πas≡Πbs′ = *-cancelˡ-≡ (product as) (product bs′) a {{prime⇒nonZero prime[a]}} $ begin
        a * product as  ≡⟨ Πas≡Πbs ⟩
        product bs      ≡⟨ product-↭ bs↭a∷bs′ ⟩
        a * product bs′ ∎
        where open ≡-Reasoning

      prime[bs'] : All Prime bs′
      prime[bs'] = All.tail (All-resp-↭ bs↭a∷bs′ prime[bs])

      a∷as↭bs : a ∷ as ↭ bs
      a∷as↭bs = begin
        a ∷ as  <⟨ factorisationUnique′ as bs′ Πas≡Πbs′ prime[as] prime[bs'] ⟩
        a ∷ bs′ ↭⟨ bs↭a∷bs′ ⟨
        bs      ∎
        where open PermutationReasoning

factorisationUnique : (f f′ : PrimeFactorisation n) → factors f ↭ factors f′
factorisationUnique {n} f f′ =
  factorisationUnique′ (factors f) (factors f′) Πf≡Πf′ (factorsPrime f) (factorsPrime f′)
  where
    Πf≡Πf′ : product (factors f) ≡ product (factors f′)
    Πf≡Πf′ = begin
      product (factors f)  ≡⟨ isFactorisation f ⟨
      n                    ≡⟨ isFactorisation f′ ⟩
      product (factors f′) ∎
      where open ≡-Reasoning

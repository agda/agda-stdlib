------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorisation of natural numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorisation where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base
open import Data.Nat.Divisibility using (_∣_; _∣?_; quotient; quotient∣n; ∣-trans; ∣1⇒≡1; divides; quotient-<; m|n⇒n≡m*quotient; hasNonTrivialDivisor; quotient≢0; quotient-∣; quotient>1)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-Rec; <-rec)
open import Data.Nat.Primality using (Prime; prime; euclidsLemma; prime⇒irreducible; prime⇒nonZero; _Rough_; 2-rough; ∤⇒rough-suc; rough∧∣⇒prime; ¬prime[1]; rough∧∣⇒rough)
open import Data.Product as Π using (∃-syntax; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; _++_; product)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Permutation.Propositional as ↭
  using (_↭_; prep; swap; ↭-refl; refl; module PermutationReasoning)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (product-↭; All-resp-↭; shift)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_$_; _∘_; _|>_; flip)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

------------------------------------------------------------------------
-- Core definition

record PrimeFactorisation (n : ℕ) : Set where
  field
    factors : List ℕ
    isFactorisation : product factors ≡ n
    factorsPrime : All Prime factors

open PrimeFactorisation public using (factors)
open PrimeFactorisation

------------------------------------------------------------------------
-- Finding a factorisation

-- this builds up three important things:
-- * a proof that every number we've gotten to so far has increasingly higher
--   possible least prime factor, so we don't have to repeat smaller factores
--   over and over (this is the "m" and "rough" parameters)
-- * a witness that this limit is getting closer to the number of interest, in a
--   way that helps the termination checker (the "k" and "eq" parameters)
-- * a proof that we can factorise any smaller number, which is useful when we
--   encounter a factor, as we can then divide by that factor and continue from
--   there without termination issues

private
  pattern 2+ n = suc (suc n)
  pattern 2≤2+n = s≤s (s≤s z≤n)
  pattern 1<2+n = 2≤2+n

factorise : ∀ n → .{{NonZero n}} → PrimeFactorisation n
factorise 1 = record
  { factors = []
  ; isFactorisation = refl
  ; factorsPrime = []
  }
factorise (2+ n₀) = <-rec P facRec (2+ n₀) 2-rough n₀ refl
  where
  P : ℕ → Set
  P n = ∀ {m} → .{{NonTrivial n}} → .{{NonTrivial m}} → m Rough n → (k : ℕ) → (n ≡ m + k) → PrimeFactorisation n

  facRec : ∀ n → <-Rec P n → P n
  -- Case 1: m = n, ∴ Prime n
  facRec (2+ _) rec {m} rough zero eq rewrite eq | +-identityʳ m = record
    { factors = m ∷ []
    ; isFactorisation = *-identityʳ m
    ; factorsPrime = prime rough ∷ []
    }
  facRec n@(2+ _) rec {m@(2+ _)} rough (suc k) eq with m ∣? n
  -- Case 2: m ∤ n, try larger m
  ... | no m∤n = facRec n rec (∤⇒rough-suc m∤n rough) k (trans eq (+-suc m k))
  -- Case 3: m ∣ n: record m and recurse on the quotient
  ... | yes m∣n = record
    { factors = m ∷ ps
    ; isFactorisation = m*Πps≡n
    ; factorsPrime = rough∧∣⇒prime rough m∣n ∷ primes
    }
    where
      m<n : m < n
      m<n = begin-strict
        m         <⟨ m<m+n m (s≤s z≤n) ⟩
        m + suc k ≡˘⟨ eq ⟩
        n ∎
        where open ≤-Reasoning
      q = quotient m∣n
      q<n = quotient-< m∣n
      n≡m*q = m|n⇒n≡m*quotient m∣n
      instance _ = n>1⇒nonTrivial (quotient>1 m∣n m<n)
      m≤q = ≮⇒≥ (λ q<m → rough record { divisor-< = q<m; divisor-∣ = quotient-∣ m∣n})

      factorisation[q] : PrimeFactorisation q
      factorisation[q] = rec q<n (rough∧∣⇒rough rough (quotient-∣ m∣n)) (q ∸ m) (sym (m+[n∸m]≡n m≤q)) 

      ps = factors factorisation[q]
      primes = factorsPrime factorisation[q]
      Πps≡q = isFactorisation factorisation[q]

      m*Πps≡n : m * product ps ≡ n
      m*Πps≡n = begin
        m * product ps ≡⟨ cong (m *_) Πps≡q ⟩
        m * q          ≡˘⟨ n≡m*q ⟩
        n ∎
        where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of a factorisation

factorisation≥1 : ∀ {as} → All Prime as → product as ≥ 1
factorisation≥1 {[]} [] = s≤s z≤n
factorisation≥1 {suc a ∷ as} (pa ∷ asPrime) = *-mono-≤ {1} {1 + a} (s≤s z≤n) (factorisation≥1 asPrime)

factorisationHasAllPrimeFactors : ∀ {as} {p} → Prime p → p ∣ product as → All Prime as → p ∈ as
factorisationHasAllPrimeFactors {[]} {2+ p} pPrime p∣Πas [] = contradiction (∣1⇒≡1 p∣Πas) λ ()
factorisationHasAllPrimeFactors {a ∷ as} {p} pPrime p∣aΠas (aPrime ∷ asPrime) with euclidsLemma a (product as) pPrime p∣aΠas
... | inj₂ p∣Πas = there (factorisationHasAllPrimeFactors pPrime p∣Πas asPrime)
... | inj₁ p∣a with prime⇒irreducible aPrime p∣a
...   | inj₁ refl = contradiction pPrime ¬prime[1]
...   | inj₂ refl = here refl

factorisationUnique′ : (as bs : List ℕ) → product as ≡ product bs → All Prime as → All Prime bs → as ↭ bs
factorisationUnique′ [] [] Πas≡Πbs asPrime bsPrime = refl
factorisationUnique′ [] (suc (suc b) ∷ bs) Πas≡Πbs asPrime (bPrime ∷ bsPrime) =
  contradiction Πas≡Πbs (<⇒≢ Πas<Πbs)
  where
    Πas<Πbs : product [] < product (2+ b ∷ bs)
    Πas<Πbs = begin-strict
      1                    ≡⟨⟩
      1       * 1          <⟨ *-monoˡ-< 1 {1} {2 + b} 1<2+n ⟩
      (2 + b) * 1          ≤⟨ *-monoʳ-≤ (2 + b) (factorisation≥1 bsPrime) ⟩
      2+ b    * product bs ≡⟨⟩
      product (2+ b ∷ bs)  ∎
      where open ≤-Reasoning

factorisationUnique′ (a ∷ as) bs Πas≡Πbs (aPrime ∷ asPrime) bsPrime = a∷as↭bs
  where
    a∣Πbs : a ∣ product bs
    a∣Πbs = divides (product as) $ begin
      product bs       ≡˘⟨ Πas≡Πbs ⟩
      product (a ∷ as) ≡⟨⟩
      a * product as   ≡⟨ *-comm a (product as) ⟩
      product as * a   ∎
      where open ≡-Reasoning

    shuffle : ∃[ bs′ ] bs ↭ a ∷ bs′
    shuffle with ys , zs , p ← ∈-∃++ (factorisationHasAllPrimeFactors aPrime a∣Πbs bsPrime)
      = ys ++ zs , ↭.↭-trans (↭.↭-reflexive p) (shift a ys zs)

    bs′ = proj₁ shuffle
    bs↭a∷bs′ = proj₂ shuffle

    Πas≡Πbs′ : product as ≡ product bs′
    Πas≡Πbs′ = *-cancelˡ-≡ (product as) (product bs′) a {{prime⇒nonZero aPrime}} $ begin
      a * product as  ≡⟨ Πas≡Πbs ⟩
      product bs      ≡⟨ product-↭ bs↭a∷bs′ ⟩
      a * product bs′ ∎
      where open ≡-Reasoning

    bs′Prime : All Prime bs′
    bs′Prime = All.tail (All-resp-↭ bs↭a∷bs′ bsPrime)

    a∷as↭bs : a ∷ as ↭ bs
    a∷as↭bs = begin
      a ∷ as  <⟨ factorisationUnique′ as bs′ Πas≡Πbs′ asPrime bs′Prime ⟩
      a ∷ bs′ ↭˘⟨ bs↭a∷bs′ ⟩
      bs      ∎
      where open PermutationReasoning

factorisationUnique : {n : ℕ} (f f′ : PrimeFactorisation n) → factors f ↭ factors f′
factorisationUnique {n} f f′ =
  factorisationUnique′ (factors f) (factors f′) Πf≡Πf′ (factorsPrime f) (factorsPrime f′)
  where
    Πf≡Πf′ : product (factors f) ≡ product (factors f′)
    Πf≡Πf′ = begin
      product (factors f)  ≡⟨ isFactorisation f ⟩
      n                    ≡˘⟨ isFactorisation f′ ⟩
      product (factors f′) ∎
      where open ≡-Reasoning

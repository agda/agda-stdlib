------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorisation of natural numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorisation where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base
open import Data.Nat.Divisibility using (_∣_; _∣?_; quotient; ∣-trans; ∣1⇒≡1; divides; quotient-<; m|n⇒n≡m*quotient; hasNonTrivialDivisor; quotient≢0; quotient-∣; quotient>1)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-Rec; <-rec; <-recBuilder)
open import Data.Nat.Primality using (Prime; prime; euclidsLemma; prime⇒irreducible; prime⇒nonZero; _Rough_; 2-rough; ∤⇒rough-suc; rough∧∣⇒prime; ¬prime[1]; rough∧∣⇒rough; rough∧>square⇒prime)
open import Data.Product as Π using (∃-syntax; _×_; _,_; proj₁; proj₂)
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
open import Induction using (build)
open import Induction.Lexicographic using (_⊗_; [_⊗_])
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
factorise n₀@(2+ _) = build [ <-recBuilder ⊗ <-recBuilder ] P facRec (n₀ , suc n₀ ∸ 4) 2-rough refl
  where
  P : ℕ × ℕ → Set
  P (n , k) = ∀ {m} → .{{NonTrivial n}} → .{{NonTrivial m}} → m Rough n → suc n ∸ m * m ≡ k → PrimeFactorisation n

  facRec : ∀ n×k → (<-Rec ⊗ <-Rec) P n×k → P n×k
  -- Case 1: m * m > n, ∴ Prime n
  facRec (n , zero) _ rough eq = record
    { factors = n ∷ []
    ; isFactorisation = *-identityʳ n
    ; factorsPrime = rough∧>square⇒prime rough (m∸n≡0⇒m≤n eq) ∷ []
    }
  facRec (n@(2+ _) , suc k) (recFactor , recQuotient) {m@(2+ _)} rough eq with m ∣? n
  -- Case 2: m ∤ n, try larger m, reducing k accordingly
  ... | no m∤n = recFactor (≤-<-trans (m∸n≤m k (2 * m)) (n<1+n k)) {suc m} (∤⇒rough-suc m∤n rough) $ begin
    suc n ∸ (suc m + m * suc m)   ≡⟨ cong (λ # → suc n ∸ (suc m + #)) (*-suc m m) ⟩
    suc n ∸ (suc m + (m + m * m)) ≡˘⟨ cong (suc n ∸_) (+-assoc (suc m) m (m * m)) ⟩
    suc n ∸ (suc (m + m) + m * m) ≡⟨ cong (suc n ∸_) (+-comm (suc (m + m)) (m * m)) ⟩
    suc n ∸ (m * m + suc (m + m)) ≡˘⟨ cong (λ # → suc n ∸ (m * m + suc (m + #))) (+-identityʳ m) ⟩
    suc n ∸ (m * m + suc (2 * m)) ≡˘⟨ ∸-+-assoc (suc n) (m * m) (suc (2 * m)) ⟩
    (suc n ∸ m * m) ∸ suc (2 * m) ≡⟨ cong (_∸ suc (2 * m)) eq ⟩
    suc k ∸ suc (2 * m)           ∎
    where open ≡-Reasoning
  -- Case 3: m ∣ n, record m and recurse on the quotient
  ... | yes m∣n = record
    { factors = m ∷ ps
    ; isFactorisation = m*Πps≡n
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
      Πps≡q = isFactorisation factorisation[q]
      m*Πps≡n : m * product ps ≡ n
      m*Πps≡n = begin
        m * product ps ≡⟨ cong (m *_) Πps≡q ⟩
        m * q          ≡˘⟨ m|n⇒n≡m*quotient m∣n ⟩
        n              ∎
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

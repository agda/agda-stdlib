------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorisation of natural numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorisation where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base
open import Data.Nat.Divisibility using (_∣_; _∣?_; quotient; quotient∣n; ∣-trans; ∣1⇒≡1; divides)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-Rec; <-rec)
open import Data.Nat.Primality using (Prime; euclidsLemma; ∣p⇒≡1∨≡p; Prime⇒NonZero)
open import Data.Nat.Primality.Rough using (_Rough_; 2-rough; extend-∤; roughn∧∣n⇒prime)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)

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
--   over and over (this is the "k" and "k-rough-n" parameters)
-- * a witness that this limit is getting closer to the number of interest, in a
--   way that helps the termination checker (the k≤n parameter)
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
factorise (2+ n) = <-rec P factoriseRec (2 + n) {2} 2≤2+n (≤⇒≤‴ 2≤2+n) 2-rough
  where

  P : ℕ → Set
  P n′ = ∀ {k} → 2 ≤ n′ → k ≤‴ n′ → k Rough n′ → PrimeFactorisation n′

  factoriseRec : ∀ n → <-Rec P n → P n
  factoriseRec (2+ n) rec (s≤s (s≤s n≤z)) ≤‴-refl k-rough-n = record
    { factors = 2 + n ∷ []
    ; isFactorisation = *-identityʳ (2 + n)
    ; factorsPrime = k-rough-n ∷ []
    }
  factoriseRec (2+ n) rec {0} 2≤2+n (≤‴-step (≤‴-step k<n)) k-rough-n =
    factoriseRec (2+ n) rec 2≤2+n k<n 2-rough
  factoriseRec (2+ n) rec {1} 2≤2+n (≤‴-step k<n) k-rough-n =
    factoriseRec (2+ n) rec 2≤2+n k<n 2-rough
  factoriseRec (2+ n) rec {suc (suc k)} 2≤2+n (≤‴-step k<n) k-rough-n with 2 + k ∣? 2+ n
  ... | no  k∤n = factoriseRec (2+ n) rec {3 + k} 2≤2+n k<n (extend-∤ k-rough-n k∤n)
  ... | yes k∣n = record
    { factors = 2 + k ∷ factors res
    ; isFactorisation = prop
    ; factorsPrime = roughn∧∣n⇒prime k-rough-n 2≤2+n k∣n ∷ factorsPrime res
    }
    where
      open ≤-Reasoning

      q : ℕ
      q = quotient k∣n

      -- we know that k < n, so if q is 0 or 1 then q * k < n
      2≤q : 2 ≤ q
      2≤q = ≮⇒≥ (λ q<2 → contradiction (_∣_.equality k∣n) (>⇒≢ (prf (≤-pred q<2)))) where

        prf : q ≤ 1 → q * 2+ k < 2 + n
        prf q≤1 = begin-strict
          q * 2+ k  ≤⟨ *-monoˡ-≤ (2 + k) q≤1 ⟩
          2 + k + 0 ≡⟨ +-identityʳ (2 + k) ⟩
          2 + k     <⟨ ≤‴⇒≤ k<n ⟩
          2 + n     ∎

      0<q : 0 < q
      0<q = begin-strict
        0 <⟨ s≤s z≤n ⟩
        2 ≤⟨ 2≤q ⟩
        q ∎

      q<n : q < 2 + n
      q<n = begin-strict
        q           <⟨ m<m*n q (2 + k) ⦃ >-nonZero 0<q ⦄ 2≤2+n ⟩
        q * (2 + k) ≡˘⟨ _∣_.equality k∣n ⟩
        2 + n       ∎

      q≮2+k : q ≮ 2 + k
      q≮2+k q<k = k-rough-n 2≤q q<k (quotient∣n k∣n)

      res : PrimeFactorisation q
      res = rec q q<n {2 + k} 2≤q (≤⇒≤‴ (≮⇒≥ q≮2+k))
          $ λ {d} d<k d-prime → k-rough-n d<k d-prime ∘ flip ∣-trans (quotient∣n k∣n)

      prop : (2 + k) * product (factors res) ≡ 2 + n
      prop = begin-equality
        (2 + k) * product (factors res)
          ≡⟨ cong ((2 + k) *_) (isFactorisation res) ⟩
        (2 + k) * q
          ≡⟨ *-comm (2 + k) q ⟩
        q * (2 + k)
          ≡˘⟨ _∣_.equality k∣n ⟩
        2 + n ∎

------------------------------------------------------------------------
-- Properties of a factorisation

factorisation≥1 : ∀ {as} → All Prime as → product as ≥ 1
factorisation≥1 {[]} [] = s≤s z≤n
factorisation≥1 {suc a ∷ as} (pa ∷ asPrime) = *-mono-≤ {1} {1 + a} (s≤s z≤n) (factorisation≥1 asPrime)

factorisationHasAllPrimeFactors : ∀ {as} {p} → Prime p → p ∣ product as → All Prime as → p ∈ as
factorisationHasAllPrimeFactors {[]} {2+ p} pPrime p∣Πas [] = contradiction (∣1⇒≡1 p∣Πas) λ ()
factorisationHasAllPrimeFactors {a ∷ as} {p} pPrime p∣aΠas (aPrime ∷ asPrime) with euclidsLemma a (product as) pPrime p∣aΠas
... | inj₂ p∣Πas = there (factorisationHasAllPrimeFactors pPrime p∣Πas asPrime)
... | inj₁ p∣a with ∣p⇒≡1∨≡p p aPrime p∣a
...   | inj₁ refl = ⊥-elim pPrime
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
    Πas≡Πbs′ = *-cancelˡ-≡ (product as) (product bs′) a {{Prime⇒NonZero aPrime}} $ begin
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

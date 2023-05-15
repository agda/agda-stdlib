------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorisation of natural numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorisation where

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Nat.Primality
open import Data.Nat.Rough
open import Data.Product as Π
open import Data.List.Base
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Binary.Permutation.Propositional as ↭
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Sum.Base
open import Function.Base
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as ≡

-- Core definition
------------------------------------------------------------------------

record Factorisation (n : ℕ) : Set where
  field
    factors : List ℕ
    isFactorisation : product factors ≡ n
    factorsPrime : All Prime factors

open Factorisation public using (factors)

-- Finding a factorisation
------------------------------------------------------------------------

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

factorise : ∀ n → .{{NonZero n}} → Factorisation n
factorise 1 = record
  { factors = []
  ; isFactorisation = refl
  ; factorsPrime = []
  }
factorise (2+ n) = <-rec P factoriseRec (2 + n) {2} 2≤2+n (≤⇒≤‴ 2≤2+n) (2-rough-n (2 + n))
  where

  P : ℕ → Set
  P n′ = ∀ {k} → 2 ≤ n′ → k ≤‴ n′ → k Rough n′ → Factorisation n′

  factoriseRec : ∀ n → <-Rec P n → P n
  factoriseRec (2+ n) rec (s≤s (s≤s n≤z)) ≤‴-refl k-rough-n = record
    { factors = 2 + n ∷ []
    ; isFactorisation = *-identityʳ (2 + n)
    ; factorsPrime = k-rough-n ∷ []
    }
  factoriseRec (2+ n) rec {0} 2≤2+n (≤‴-step (≤‴-step k<n)) k-rough-n =
    factoriseRec (2+ n) rec 2≤2+n k<n (2-rough-n (2+ n))
  factoriseRec (2+ n) rec {1} 2≤2+n (≤‴-step k<n) k-rough-n =
    factoriseRec (2+ n) rec 2≤2+n k<n (2-rough-n (2+ n))
  factoriseRec (2+ n) rec {suc (suc k)} 2≤2+n (≤‴-step k<n) k-rough-n with 2 + k ∣? 2+ n
  ... | no  k∤n = factoriseRec (2+ n) rec {3 + k} 2≤2+n k<n (extend-∤ k-rough-n k∤n)
  ... | yes k∣n = record
    { factors = 2 + k ∷ Factorisation.factors res
    ; isFactorisation = prop
    ; factorsPrime = roughn∧∣n⇒prime k-rough-n 2≤2+n k∣n ∷ Factorisation.factorsPrime res
    }
    where
      -- we know that k < n, so if q is 0 or 1 then q * k < n
      2≤q : 2 ≤ quotient k∣n
      2≤q = ≮⇒≥ (λ q<2 → contradiction (_∣_.equality k∣n) (>⇒≢ (prf (≤-pred q<2)))) where

        prf : quotient k∣n ≤ 1 → k∣n .quotient * 2+ k < 2+ n
        prf q≤1 = let open ≤-Reasoning in begin-strict
          k∣n .quotient * 2+ k ≤⟨ *-monoˡ-≤ (2 + k) q≤1 ⟩
          2 + k + 0            ≡⟨ +-identityʳ (2 + k) ⟩
          2 + k                <⟨ ≤‴⇒≤ k<n ⟩
          2 + n                ∎

      q<n : quotient k∣n < 2+ n
      q<n = <-transˡ (m<m*n (quotient k∣n) (2 + k) ⦃ >-nonZero (<-transˡ (s≤s z≤n) 2≤q) ⦄ 2≤2+n) (≤-reflexive (sym (_∣_.equality k∣n)))

      res : Factorisation (quotient k∣n)
      res = rec (quotient k∣n) q<n {2 + k} 2≤q (≤⇒≤‴ (≮⇒≥ (λ q<k → k-rough-n 2≤q q<k (quotient∣n k∣n)))) λ {d} d<k d-prime → k-rough-n d<k d-prime ∘ flip ∣-trans (quotient∣n k∣n)

      prop : (2 + k) * product (factors res) ≡ 2 + n
      prop = let open ≡-Reasoning in begin
        (2 + k) * product (factors res) ≡⟨ cong ((2 + k) *_) (Factorisation.isFactorisation res) ⟩
        (2 + k) * quotient k∣n          ≡⟨ *-comm (2 + k) (quotient k∣n) ⟩
        quotient k∣n * (2 + k)          ≡˘⟨ _∣_.equality k∣n ⟩
        2 + n                           ∎

------------------------------------------------------------------------
-- Properties of a factorisation

factorisation≥1 : ∀ {as} → All Prime as → product as ≥ 1
factorisation≥1 {[]} [] = s≤s z≤n
factorisation≥1 {suc a ∷ as} (pa ∷ asPrime) = *-mono-≤ {1} {1 + a} (s≤s z≤n) (factorisation≥1 asPrime)

factorisationPullToFront : ∀ {as} {p} → Prime p → p ∣ product as → All Prime as → ∃[ as′ ] as ↭ (p ∷ as′)
factorisationPullToFront {[]} {suc (suc p)} pPrime p∣Πas asPrime = contradiction (∣1⇒≡1 p∣Πas) λ ()
factorisationPullToFront {a ∷ as} {p} pPrime p∣aΠas (aPrime ∷ asPrime) with euclidsLemma a (product as) pPrime p∣aΠas
... | inj₂ p∣Πas = Π.map (a ∷_) (λ as↭p∷as′ → ↭-trans (prep a as↭p∷as′) (↭.swap a p refl)) (factorisationPullToFront pPrime p∣Πas asPrime)
... | inj₁ p∣a with ∣p⇒≡1∨≡p p aPrime p∣a
...   | inj₁ refl = ⊥-elim pPrime
...   | inj₂ refl = as , ↭-refl

factorisationUnique′ : (as bs : List ℕ) → product as ≡ product bs → All Prime as → All Prime bs → as ↭ bs
factorisationUnique′ [] [] Πas≡Πbs asPrime bsPrime = refl
factorisationUnique′ [] (suc (suc b) ∷ bs) Πas≡Πbs asPrime (bPrime ∷ bsPrime) = contradiction Πas≡Πbs (<⇒≢ (<-transˡ (*-monoˡ-< 1 {1} {2 + b} 2≤2+n) (*-monoʳ-≤ (2 + b) (factorisation≥1 bsPrime))))
factorisationUnique′ (a ∷ as) bs Πas≡Πbs (aPrime ∷ asPrime) bsPrime with bs′ , bs↭a∷bs′ ← factorisationPullToFront aPrime (divides (product as) (≡.trans (sym Πas≡Πbs) (*-comm a (product as)))) bsPrime = begin
    a ∷ as  <⟨ factorisationUnique′ as bs′
               (*-cancelˡ-≡ (product as) (product bs′) a {{Prime⇒NonZero aPrime}} (≡.trans Πas≡Πbs (productPreserves↭⇒≡ bs↭a∷bs′)))
               asPrime
               (All.tail (All-resp-↭ bs↭a∷bs′ bsPrime))
            ⟩
    a ∷ bs′ ↭˘⟨ bs↭a∷bs′ ⟩
    bs      ∎
  where open PermutationReasoning

factorisationUnique : {n : ℕ} (f f′ : Factorisation n) → factors f ↭ factors f′
factorisationUnique f f′ = factorisationUnique′ (factors f) (factors f′) (≡.trans (Factorisation.isFactorisation f) (sym (Factorisation.isFactorisation f′))) (Factorisation.factorsPrime f) (Factorisation.factorsPrime f′)

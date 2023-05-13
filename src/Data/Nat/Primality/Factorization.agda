------------------------------------------------------------------------
-- The Agda standard library
--
-- Prime factorization of naturla numbers and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Factorization where

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

record Factorization (n : ℕ) : Set where
  field
    factors : List ℕ
    isFactorization : product factors ≡ n
    factorsPrime : All Prime factors

open Factorization public using (factors)

-- Finding a factorization
------------------------------------------------------------------------

-- this builds up three important things:
-- * a proof that every number we've gotten to so far has increasingly higher
--   possible least prime factor, so we don't have to repeat smaller factores
--   over and over (this is the "k" and "k-rough-n" parameters)
-- * a witness that this limit is getting closer to the number of interest, in a
--   way that helps the termination checker (the k≤n parameter)
-- * a proof that we can factorize any smaller number, which is useful when we
--   encounter a factor, as we can then divide by that factor and continue from
--   there without termination issues

factorize : ∀ n → .{{NonZero n}} → Factorization n
factorize 1 = record
  { factors = []
  ; isFactorization = refl
  ; factorsPrime = []
  }
factorize (suc (suc n)) = <-rec (λ n′ → ∀ {k} → 2 ≤ n′ → k ≤‴ n′ → k Rough n′ → Factorization n′) factorizeRec (2 + n) {2} (s≤s (s≤s z≤n)) (≤⇒≤‴ (s≤s (s≤s z≤n))) (2-rough-n (2 + n))
  where
  factorizeRec : ∀ n → <-Rec (λ n′ → ∀ {k} → 2 ≤ n′ → k ≤‴ n′ → k Rough n′ → Factorization n′) n → ∀ {k} → 2 ≤ n → k ≤‴ n → k Rough n → Factorization n
  factorizeRec (suc (suc n)) rec (s≤s (s≤s n≤z)) ≤‴-refl k-rough-n = record
    { factors = 2 + n ∷ []
    ; isFactorization = *-identityʳ (2 + n)
    ; factorsPrime = (λ 2≤d d<n d∣n → rough⇒∤ k-rough-n 2≤d d<n d∣n) ∷ []
    }
  factorizeRec (suc (suc n)) rec {0} (s≤s (s≤s z≤n)) (≤‴-step (≤‴-step k<n)) k-rough-n = factorizeRec (2 + n) rec (s≤s (s≤s z≤n)) k<n (2-rough-n (2 + n))
  factorizeRec (suc (suc n)) rec {1} (s≤s (s≤s z≤n)) (≤‴-step k<n) k-rough-n = factorizeRec (2 + n) rec (s≤s (s≤s z≤n)) k<n (2-rough-n (2 + n))
  factorizeRec (suc (suc n)) rec {suc (suc k)} (s≤s (s≤s z≤n)) (≤‴-step k<n) k-rough-n with 2 + k ∣? 2 + n
  ... | no  k∤n = factorizeRec (2 + n) rec {3 + k} (s≤s (s≤s z≤n)) k<n (extend-∤ k-rough-n k∤n)
  ... | yes k∣n = record
    { factors = 2 + k ∷ Factorization.factors res
    ; isFactorization = prop
    ; factorsPrime = roughn∧∣n⇒prime k-rough-n (s≤s (s≤s z≤n)) k∣n ∷ Factorization.factorsPrime res
    }
    where
      open ≡-Reasoning
  
      -- we know that k < n, so if q is 0 or 1 then q * k < n
      2≤q : 2 ≤ quotient k∣n
      2≤q = ≮⇒≥ λ { (s≤s q≤1) → >⇒≢ (<-transʳ (*-monoˡ-≤ (2 + k) q≤1) (<-transʳ (≤-reflexive (+-identityʳ (2 + k))) (≤‴⇒≤ k<n))) (_∣_.equality k∣n) }
  
      q<n : quotient k∣n < 2 + n
      q<n = <-transˡ (m<m*n (quotient k∣n) (2 + k) ⦃ >-nonZero (<-transˡ (s≤s z≤n) 2≤q) ⦄ (s≤s (s≤s z≤n))) (≤-reflexive (sym (_∣_.equality k∣n)))

      res : Factorization (quotient k∣n)
      res = rec (quotient k∣n) q<n {2 + k} 2≤q (≤⇒≤‴ (≮⇒≥ (λ q<k → rough⇒∤ k-rough-n 2≤q q<k (quotient∣n k∣n)))) λ {d} d<k d-prime → k-rough-n d<k d-prime ∘ flip ∣-trans (quotient∣n k∣n)

      prop : (2 + k) * product (factors res) ≡ 2 + n
      prop = begin
        (2 + k) * product (factors res) ≡⟨ cong ((2 + k) *_) (Factorization.isFactorization res) ⟩
        (2 + k) * quotient k∣n          ≡⟨ *-comm (2 + k) (quotient k∣n) ⟩
        quotient k∣n * (2 + k)          ≡˘⟨ _∣_.equality k∣n ⟩
        2 + n                           ∎

factorization≥1 : ∀ {as} → All Prime as → product as ≥ 1
factorization≥1 {[]} [] = s≤s z≤n
factorization≥1 {suc a ∷ as} (pa ∷ asPrime) = *-mono-≤ {1} {1 + a} (s≤s z≤n) (factorization≥1 asPrime)

factorizationPullToFront : ∀ {as} {p} → Prime p → p ∣ product as → All Prime as → ∃[ as′ ] as ↭ (p ∷ as′)
factorizationPullToFront {[]} {suc (suc p)} pPrime p∣Πas asPrime = contradiction (∣1⇒≡1 p∣Πas) λ ()
factorizationPullToFront {a ∷ as} {p} pPrime p∣aΠas (aPrime ∷ asPrime) with euclidsLemma a (product as) pPrime p∣aΠas
... | inj₂ p∣Πas = Π.map (a ∷_) (λ as↭p∷as′ → ↭-trans (prep a as↭p∷as′) (↭.swap a p refl)) (factorizationPullToFront pPrime p∣Πas asPrime)
... | inj₁ p∣a with ∣p⇒≡1∨≡p p aPrime p∣a
...   | inj₁ refl = ⊥-elim pPrime
...   | inj₂ refl = as , ↭-refl

factorizationUnique′ : (as bs : List ℕ) → product as ≡ product bs → All Prime as → All Prime bs → as ↭ bs
factorizationUnique′ [] [] Πas≡Πbs asPrime bsPrime = refl
factorizationUnique′ [] (suc (suc b) ∷ bs) Πas≡Πbs asPrime (bPrime ∷ bsPrime) = contradiction Πas≡Πbs (<⇒≢ (<-transˡ (*-monoˡ-< 1 {1} {2 + b} (s≤s (s≤s z≤n))) (*-monoʳ-≤ (2 + b) (factorization≥1 bsPrime))))
factorizationUnique′ (a ∷ as) bs Πas≡Πbs (aPrime ∷ asPrime) bsPrime with bs′ , bs↭a∷bs′ ← factorizationPullToFront aPrime (divides (product as) (≡.trans (sym Πas≡Πbs) (*-comm a (product as)))) bsPrime = begin
    a ∷ as  <⟨ factorizationUnique′ as bs′
               (*-cancelˡ-≡ (product as) (product bs′) a {{Prime⇒NonZero aPrime}} (≡.trans Πas≡Πbs (productPreserves↭⇒≡ bs↭a∷bs′)))
               asPrime
               (All.tail (All-resp-↭ bs↭a∷bs′ bsPrime))
            ⟩
    a ∷ bs′ ↭˘⟨ bs↭a∷bs′ ⟩
    bs      ∎
  where open PermutationReasoning

factorizationUnique : {n : ℕ} (f f′ : Factorization n) → factors f ↭ factors f′
factorizationUnique f f′ = factorizationUnique′ (factors f) (factors f′) (≡.trans (Factorization.isFactorization f) (sym (Factorization.isFactorization f′))) (Factorization.factorsPrime f) (Factorization.factorsPrime f′)

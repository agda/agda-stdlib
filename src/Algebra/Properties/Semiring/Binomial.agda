------------------------------------------------------------------------
-- The Agda standard library
--
-- The Binomial Theorem for *-commuting elements in a Semiring
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semiring)
open import Data.Bool.Base using (true)
open import Data.Nat.Base as Nat hiding (_+_; _*_; _^_)
open import Data.Nat.Combinatorics
  using (_C_; nCn≡1; nC1≡n; nCk+nC[k+1]≡[n+1]C[k+1])
open import Data.Nat.Properties as Nat
  using (<⇒<ᵇ; n<1+n; n∸n≡0; +-∸-assoc)
open import Data.Fin.Base as Fin
  using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties as Fin
  using (toℕ<n; toℕ-inject₁)
open import Data.Fin.Relation.Unary.Top
  using (view; top; inj; view-inj; view-top; view-top-toℕ; module Instances)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; module ≡-Reasoning)
  renaming (refl to ≡-refl)

module Algebra.Properties.Semiring.Binomial {a ℓ} (S : Semiring a ℓ) where

open Semiring S
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Properties.Semiring.Sum S
open import Algebra.Properties.Semiring.Mult S
open import Algebra.Properties.Semiring.Exp S
import Relation.Binary.Reasoning.Setoid setoid as ≈-Reasoning


------------------------------------------------------------------------
-- The Binomial Theorem for *-commuting elements in a Semiring
-- Freely adapted from PR #1287 by Maciej Piechotka (@uzytkownik)

module _ (x y : Carrier) where

------------------------------------------------------------------------
-- Definitions

  module Binomial (n : ℕ) where

    module _ (i : Fin (suc n)) where

      private
        k   = toℕ i
        n-k = n ∸ k

      binomial : Carrier
      binomial = (x ^ k) * (y ^ n-k)

      term : Carrier
      term = (n C k) × binomial

    expansion : Carrier
    expansion = ∑[ i < suc n ] term i

    term₁ : (i : Fin (suc (suc n))) → Carrier
    term₁ zero    = 0#
    term₁ (suc i) = x * term i

    sum₁ : Carrier
    sum₁ = ∑[ i < suc (suc n) ] term₁ i

    term₂ : (i : Fin (suc (suc n))) → Carrier
    term₂ i with view i
    ... | top   = 0#
    ... | inj j = y * term j

    sum₂ : Carrier
    sum₂ = ∑[ i < suc (suc n) ] term₂ i

------------------------------------------------------------------------
-- Properties

  module BinomialLemmas (n : ℕ) where

    open Binomial n

    open ≈-Reasoning

    lemma₁ : x * expansion ≈ sum₁
    lemma₁ = begin
      x * expansion
        ≈⟨ *-distribˡ-sum x term ⟩
      ∑[ i < suc n ] (x * term i)
        ≈˘⟨ +-identityˡ _ ⟩
      (0# + ∑[ i < suc n ] (x * term i))
        ≡⟨⟩
      (0# + ∑[ i < suc n ] term₁ (suc i))
        ≡⟨⟩
      sum₁  ∎

    lemma₂ : y * expansion ≈ sum₂
    lemma₂ = begin
      (y * expansion)
        ≈⟨ *-distribˡ-sum y term ⟩
      ∑[ i < suc n ] (y * term i)
        ≈˘⟨ +-identityʳ _ ⟩
      ∑[ i < suc n ] (y * term i) + 0#
        ≈⟨ +-cong (sum-cong-≋ lemma₂-inj) lemma₂-top ⟩
      (∑[ i < suc n ] term₂-inj i) + term₂ [n+1]
        ≈˘⟨ sum-init-last term₂ ⟩
      sum term₂
        ≡⟨⟩
      sum₂  ∎
      where
        [n+1] = fromℕ (suc n)

        lemma₂-top : 0# ≈ term₂ [n+1]
        lemma₂-top rewrite view-top (suc n) = refl

        term₂-inj : (i : Fin (suc n)) → Carrier
        term₂-inj i = term₂ (inject₁ i)

        lemma₂-inj : ∀ i → y * term i ≈ term₂-inj i
        lemma₂-inj i rewrite view-inj i = refl

------------------------------------------------------------------------
-- Next, a lemma which is independent of commutativity

  module _ {n} (i : Fin (suc n)) where

    open Binomial n using (term)

    private

      k = toℕ i

    x*lemma : x * term i ≈ (n C k) × Binomial.binomial (suc n) (suc i)
    x*lemma = begin
      x * term i                                  ≡⟨⟩
      x * ((n C k) × (x ^ k * y ^ (n ∸ k)))       ≈˘⟨ *-congˡ (×-assoc-* (n C k) _ _) ⟩
      x * ((n C k) × x ^ k * y ^ (n ∸ k))         ≈˘⟨ *-assoc x ((n C k) × x ^ k) _ ⟩
      (x * (n C k) × x ^ k) * y ^ (n ∸ k)         ≈⟨ *-congʳ (×-comm-* (n C k) _ _) ⟩
      (n C k) × x ^ (suc k) * y ^ (n ∸ k)         ≡⟨⟩
      (n C k) × x ^ (suc k) * y ^ (suc n ∸ suc k) ≈⟨ ×-assoc-* (n C k) _ _ ⟩
      (n C k) × Binomial.binomial (suc n) (suc i) ∎
      where
        open ≈-Reasoning



------------------------------------------------------------------------
-- Next, a lemma which does require commutativity

  module _ (x*y≈y*x : x * y ≈ y * x) where

    module _ {n : ℕ} (j : Fin n) where

      open Binomial n using (binomial; term)

      private

        i = inject₁ j

      y*lemma : y * term (suc j) ≈ (n C toℕ (suc j)) × Binomial.binomial (suc n) (suc i)
      y*lemma = begin
        y * term (suc j)
          ≈⟨ ×-comm-* nC[j+1] y (binomial (suc j)) ⟩
        nC[j+1] × (y * binomial (suc j))
          ≈⟨ ×-congʳ nC[j+1] (y*x^m*y^n≈x^m*y^[n+1] x*y≈y*x [j+1] [n-j-1]) ⟩
        nC[j+1] × (x ^ [j+1] * y ^ [n-j])
          ≈˘⟨ ×-congʳ nC[j+1] (*-congʳ (^-congʳ x [k+1]≡[j+1])) ⟩
        nC[j+1] × (x ^ [k+1] * y ^ [n-j])
          ≈˘⟨ ×-congʳ nC[j+1] (*-congˡ (^-congʳ y [n-k]≡[n-j])) ⟩
        nC[j+1] × (x ^ [k+1] * y ^ [n-k])
          ≡⟨⟩
        nC[j+1] × (x ^ [k+1] * y ^ [n+1]-[k+1])
          ≡⟨⟩
        (n C toℕ (suc j)) × Binomial.binomial (suc n) (suc i) ∎
        where
          k           = toℕ i
          k≡j         : k ≡ toℕ j
          k≡j         = toℕ-inject₁ j

          [k+1]       = ℕ.suc k
          [j+1]       = toℕ (suc j)
          [n-k]       = n ∸ k
          [n+1]-[k+1] = [n-k]
          [n-j-1]     = n ∸ [j+1]
          [n-j]       = ℕ.suc [n-j-1]
          nC[j+1]     = n C [j+1]

          [k+1]≡[j+1] : [k+1] ≡ [j+1]
          [k+1]≡[j+1] = cong suc k≡j

          [n-k]≡[n-j] : [n-k] ≡ [n-j]
          [n-k]≡[n-j] = begin
            [n-k]       ≡⟨ cong (n ∸_) k≡j ⟩
            n ∸ toℕ j  ≡⟨ +-∸-assoc 1 (toℕ<n j) ⟩
            [n-j]       ∎ where open ≡-Reasoning
          open ≈-Reasoning

------------------------------------------------------------------------
-- Now, a lemma characterising the sum of the term₁ and term₂ expressions

    module _ n where

      open ≈-Reasoning

      open Binomial n using (term; term₁; term₂)

      private

        n<ᵇ1+n : (n Nat.<ᵇ suc n) ≡ true
        n<ᵇ1+n with n Nat.<ᵇ suc n | <⇒<ᵇ (n<1+n n)
        ... | true | _ = ≡-refl


      term₁+term₂≈term : ∀ i → term₁ i + term₂ i ≈ Binomial.term (suc n) i

      term₁+term₂≈term 0F = begin
        term₁ 0F + term₂ 0F          ≡⟨⟩
        0# + y * (1 × (1# * y ^ n))  ≈⟨ +-identityˡ _ ⟩
        y * (1 × (1# * y ^ n))       ≈⟨ *-congˡ (+-identityʳ (1# * y ^ n)) ⟩
        y * (1# * y ^ n)             ≈⟨ *-congˡ (*-identityˡ (y ^ n)) ⟩
        y * y ^ n                    ≡⟨⟩
        y ^ suc n                    ≈˘⟨ *-identityˡ (y ^ suc n) ⟩
        1# * y ^ suc n               ≈˘⟨ +-identityʳ (1# * y ^ suc n) ⟩
        1 × (1# * y ^ suc n)         ≡⟨⟩
        Binomial.term (suc n) 0F      ∎

      term₁+term₂≈term (suc i) with view i
      ... | top
      {- remembering that i = fromℕ n, definitionally -}
        rewrite view-top-toℕ i {{Instances.top⁺}}
          | nCn≡1 n
          | n∸n≡0 n
          | n<ᵇ1+n
          = begin
        x * ((x ^ n * 1#) + 0#) + 0# ≈⟨ +-identityʳ _ ⟩
        x * ((x ^ n * 1#) + 0#)      ≈⟨ *-congˡ (+-identityʳ _) ⟩
        x * (x ^ n * 1#)             ≈˘⟨ *-assoc _ _ _ ⟩
        x * x ^ n * 1#               ≈˘⟨ +-identityʳ _ ⟩
        1 × (x * x ^ n * 1#)         ∎

      ... | inj j
      {- remembering that i = inject₁ j, definitionally -}
          = begin
        (x * term i) + (y * term (suc j))
          ≈⟨ +-cong (x*lemma i) (y*lemma j) ⟩
        (nCk × [x^k+1]*[y^n-k]) + (nC[j+1] × [x^k+1]*[y^n-k])
          ≈˘⟨ +-congˡ (×-congˡ nC[k+1]≡nC[j+1]) ⟩
        (nCk × [x^k+1]*[y^n-k]) + (nC[k+1] × [x^k+1]*[y^n-k])
          ≈˘⟨ ×-homo-+ [x^k+1]*[y^n-k] nCk nC[k+1] ⟩
        (nCk Nat.+ nC[k+1]) × [x^k+1]*[y^n-k]
          ≡⟨ cong (_× [x^k+1]*[y^n-k]) (nCk+nC[k+1]≡[n+1]C[k+1] n k) ⟩
        ((suc n) C (suc k)) × [x^k+1]*[y^n-k]
          ≡⟨⟩
        Binomial.term (suc n) (suc i) ∎
          where
            k               = toℕ i
            [k+1]           = ℕ.suc k
            [j+1]           = toℕ (suc j)
            nCk             = n C k
            nC[k+1]         = n C [k+1]
            nC[j+1]         = n C [j+1]
            nC[k+1]≡nC[j+1] : nC[k+1] ≡ nC[j+1]
            nC[k+1]≡nC[j+1] = cong ((n C_) ∘ suc) (toℕ-inject₁ j)
            [x^k+1]*[y^n-k] : Carrier
            [x^k+1]*[y^n-k] = Binomial.binomial (suc n) (suc i)

------------------------------------------------------------------------
-- Finally, the main result

    open ≈-Reasoning

    theorem : ∀ n → ((x + y) ^ n) ≈ Binomial.expansion n

    theorem zero    = begin
      (x + y) ^ 0                     ≡⟨⟩
      1#                              ≈˘⟨ 1×-identityʳ 1# ⟩
      1 × 1#                          ≈˘⟨ *-identityʳ (1 × 1#) ⟩
      (1 × 1#) * 1#                   ≈⟨ ×-assoc-* 1 1# 1# ⟩
      1 × (1# * 1#)                   ≡⟨⟩
      1 × (x ^ 0 * y ^ 0)             ≈˘⟨ +-identityʳ _ ⟩
      1 × (x ^ 0 * y ^ 0) + 0#        ≡⟨⟩
      (0 C 0) × (x ^ 0 * y ^ 0) + 0#  ≡⟨⟩
      Binomial.expansion 0            ∎

    theorem n@(suc n-1) = begin
      (x + y) ^ n                         ≡⟨⟩
      (x + y) * (x + y) ^ n-1             ≈⟨ *-congˡ (theorem n-1) ⟩
      (x + y) * expansion                 ≈⟨ distribʳ _ _ _ ⟩
      x * expansion + y * expansion       ≈⟨ +-cong lemma₁ lemma₂ ⟩
      sum₁ + sum₂                         ≈˘⟨ ∑-distrib-+ term₁ term₂ ⟩
      ∑[ i < suc n ] (term₁ i + term₂ i)  ≈⟨ sum-cong-≋ (term₁+term₂≈term n-1) ⟩
      ∑[ i < suc n ] Binomial.term n i    ≡⟨⟩
      Binomial.expansion n                ∎
      where
        open Binomial n-1
        open BinomialLemmas n-1


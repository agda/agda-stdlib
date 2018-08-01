------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Rational numbers
------------------------------------------------------------------------

module Data.Rational.Properties where

open import Function using (_∘_ ; _$_)
import Data.Integer as ℤ
import Data.Integer.Properties as ℤₚ
open import Data.Rational
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; cong)

------------------------------------------------------------------------
-- _≤_

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = *≤* ℤₚ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans {i = mkℚ n₁ d₁ c₁} {j = mkℚ n₂ d₂ c₂} {k = mkℚ n₃ d₃ c₃} (*≤* eq₁) (*≤* eq₂)
  = *≤* $ ℤₚ.*-cancelʳ-≤-pos (n₁ ℤ.* ℤ.+ suc d₃) (n₃ ℤ.* ℤ.+ suc d₁) d₂ $ begin
  let sd₁ = ℤ.+ suc d₁; sd₂ = ℤ.+ suc d₂; sd₃ = ℤ.+ suc d₃ in
  (n₁  ℤ.* sd₃) ℤ.* sd₂  ≡⟨ ℤₚ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁   ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤₚ.*-comm sd₃ sd₂) ⟩
  n₁   ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ sym (ℤₚ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  ℤ.* sd₂) ℤ.* sd₃  ≤⟨ ℤₚ.*-monoʳ-≤-pos d₃ eq₁ ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤₚ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤₚ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) ≤⟨ ℤₚ.*-monoˡ-≤-pos d₁ eq₂ ⟩
  sd₁  ℤ.* (n₃  ℤ.* sd₂) ≡⟨ sym (ℤₚ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃)  ℤ.* sd₂  ≡⟨ cong (ℤ._* sd₂) (ℤₚ.*-comm sd₁ n₃) ⟩
  (n₃  ℤ.* sd₁) ℤ.* sd₂  ∎
  where open ℤₚ.≤-Reasoning

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (ℤₚ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q = [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′ (ℤₚ.≤-total
  (ℚ.numerator p ℤ.* ℚ.denominator q)
  (ℚ.numerator q ℤ.* ℚ.denominator p))

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

≤-decTotalOrder : DecTotalOrder _ _ _
≤-decTotalOrder = record
  { Carrier         = ℚ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = ≤-isDecTotalOrder
  }

≤-irrelevance : Irrelevant _≤_
≤-irrelevance (*≤* x₁) (*≤* x₂) = cong *≤* (ℤₚ.≤-irrelevance x₁ x₂)

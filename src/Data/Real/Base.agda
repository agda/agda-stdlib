------------------------------------------------------------------------
-- The Agda standard library
--
-- Real numbers
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Data.Real.Base where

open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Properties
open import Data.Integer.Base using (+<+)
open import Data.Nat.Base as ℕ using (z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product.Base hiding (map)
open import Data.Rational.Base as ℚ hiding (_+_)
open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Unnormalised using (*<*)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Function.Metric.Rational.CauchySequence d-metric public renaming (CauchySequence to ℝ)

fromℚ : ℚ → ℝ
fromℚ = embed

_+_ : ℝ → ℝ → ℝ
sequence (x + y) = zipWith ℚ._+_ (sequence x) (sequence y)
isCauchy (x + y) ε = proj₁ [x] ℕ.+ proj₁ [y] , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (zipWith ℚ._+_ (sequence x) (sequence y)) m - lookup (zipWith ℚ._+_ (sequence x) (sequence y)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣)
      (lookup-zipWith m ℚ._+_ (sequence x) (sequence y))
      (lookup-zipWith n ℚ._+_ (sequence x) (sequence y))
    ⟩
  ∣ (lookup (sequence x) m ℚ.+ lookup (sequence y) m) - (lookup (sequence x) n ℚ.+ lookup (sequence y) n) ∣
    ≡⟨ cong ∣_∣ (lemma (lookup (sequence x) m) (lookup (sequence y) m) (lookup (sequence x) n) (lookup (sequence y) n)) ⟩
  ∣ (lookup (sequence x) m - lookup (sequence x) n) ℚ.+ (lookup (sequence y) m - lookup (sequence y) n) ∣
    ≤⟨ ∣p+q∣≤∣p∣+∣q∣
      (lookup (sequence x) m - lookup (sequence x) n)
      (lookup (sequence y) m - lookup (sequence y) n)
    ⟩
  ∣ lookup (sequence x) m - lookup (sequence x) n ∣ ℚ.+ ∣ lookup (sequence y) m - lookup (sequence y) n ∣
    <⟨ +-mono-<
      (proj₂ [x]
        (ℕ.≤-trans (ℕ.m≤m+n (proj₁ [x]) (proj₁ [y])) m≥N)
        (ℕ.≤-trans (ℕ.m≤m+n (proj₁ [x]) (proj₁ [y])) n≥N)
      )
      (proj₂ [y]
        (ℕ.≤-trans (ℕ.m≤n+m (proj₁ [y]) (proj₁ [x])) m≥N)
        (ℕ.≤-trans (ℕ.m≤n+m (proj₁ [y]) (proj₁ [x])) n≥N)
      )
    ⟩
  ½ * ε ℚ.+ ½ * ε
    ≡˘⟨ *-distribʳ-+ ε ½ ½ ⟩
  1ℚ * ε
    ≡⟨ *-identityˡ ε ⟩
  ε ∎
  where
    open ≤-Reasoning
    instance _ : Positive (½ * ε)
    _ = positive {½ * ε} $ begin-strict
      0ℚ     ≡˘⟨ *-zeroˡ ε ⟩
      0ℚ * ε <⟨ *-monoˡ-<-pos ε {0ℚ} {½} (*<* (+<+ (s≤s z≤n))) ⟩
      ½ * ε  ∎
    [x] = isCauchy x (½ * ε)
    [y] = isCauchy y (½ * ε)

    lemma : ∀ a b c d → (a ℚ.+ b) - (c ℚ.+ d) ≡ (a - c) ℚ.+ (b - d)
    lemma = solve 4 (λ a b c d → ((a :+ b) :- (c :+ d)) , ((a :- c) :+ (b :- d))) refl
      where open +-*-Solver


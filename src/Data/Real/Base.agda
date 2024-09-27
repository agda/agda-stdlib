------------------------------------------------------------------------
-- The Agda standard library
--
-- Real numbers
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

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
open import Relation.Nullary

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

_*ₗ_ : ℚ → ℝ → ℝ
sequence (p *ₗ x) = map (p *_) (sequence x)
isCauchy (p *ₗ x) ε with p ≟ 0ℚ
... | yes p≡0 = 0 , λ {m} {n} _ _ → begin-strict
  ∣ lookup (map (p *_) (sequence x)) m - lookup (map (p *_) (sequence x)) n ∣ ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m (p *_) (sequence x)) (lookup-map n (p *_) (sequence x)) ⟩
  ∣ p * lookup (sequence x) m - p * lookup (sequence x) n ∣                   ≡⟨ cong (λ # → ∣ p * lookup (sequence x) m ℚ.+ # ∣) (neg-distribʳ-* p (lookup (sequence x) n)) ⟩
  ∣ p * lookup (sequence x) m ℚ.+ p * - lookup (sequence x) n ∣               ≡˘⟨ cong ∣_∣ (*-distribˡ-+ p (lookup (sequence x) m) (- lookup (sequence x) n)) ⟩
  ∣ p * (lookup (sequence x) m - lookup (sequence x) n) ∣                     ≡⟨ cong (λ # → ∣ # * (lookup (sequence x) m - lookup (sequence x) n) ∣) p≡0 ⟩
  ∣ 0ℚ * (lookup (sequence x) m - lookup (sequence x) n) ∣                    ≡⟨ cong ∣_∣ (*-zeroˡ (lookup (sequence x) m - lookup (sequence x) n)) ⟩
  ∣ 0ℚ ∣                                                                      ≡⟨⟩
  0ℚ                                                                          <⟨ positive⁻¹ ε ⟩
  ε                                                                           ∎
  where open ≤-Reasoning
... | no  p≢0 = proj₁ (isCauchy x (1/ ∣ p ∣ * ε)) , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (map (p *_) (sequence x)) m - lookup (map (p *_) (sequence x)) n ∣ ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m (p *_) (sequence x)) (lookup-map n (p *_) (sequence x)) ⟩
  ∣ p * lookup (sequence x) m - p * lookup (sequence x) n ∣                   ≡⟨ cong (λ # → ∣ p * lookup (sequence x) m ℚ.+ # ∣) (neg-distribʳ-* p (lookup (sequence x) n)) ⟩
  ∣ p * lookup (sequence x) m ℚ.+ p * - lookup (sequence x) n ∣               ≡˘⟨ cong ∣_∣ (*-distribˡ-+ p (lookup (sequence x) m) (- lookup (sequence x) n)) ⟩
  ∣ p * (lookup (sequence x) m - lookup (sequence x) n) ∣                     ≡⟨ ∣p*q∣≡∣p∣*∣q∣ p (lookup (sequence x) m - lookup (sequence x) n) ⟩
  ∣ p ∣ * ∣ lookup (sequence x) m - lookup (sequence x) n ∣                   <⟨ *-monoʳ-<-pos ∣ p ∣ (proj₂ (isCauchy x (1/ ∣ p ∣ * ε)) m≥N n≥N) ⟩
  ∣ p ∣ * (1/ ∣ p ∣ * ε)                                                      ≡˘⟨ *-assoc ∣ p ∣ (1/ ∣ p ∣) ε ⟩
  (∣ p ∣ * 1/ ∣ p ∣) * ε                                                      ≡⟨ cong (_* ε) (*-inverseʳ ∣ p ∣) ⟩
  1ℚ * ε                                                                      ≡⟨ *-identityˡ ε ⟩
  ε                                                                           ∎
  where
    open ≤-Reasoning
    instance _ : NonZero ∣ p ∣
    _ = ≢-nonZero {∣ p ∣} λ ∣p∣≡0 → p≢0 (∣p∣≡0⇒p≡0 p ∣p∣≡0)
    instance _ : Positive ∣ p ∣
    _ = nonNeg∧nonZero⇒pos ∣ p ∣ {{∣-∣-nonNeg p}}
    instance _ : Positive (1/ ∣ p ∣)
    _ = 1/pos⇒pos ∣ p ∣
    instance _ : Positive (1/ ∣ p ∣ * ε)
    _ = positive $ begin-strict
      0ℚ            ≡˘⟨ *-zeroʳ (1/ ∣ p ∣) ⟩
      1/ ∣ p ∣ * 0ℚ <⟨ *-monoʳ-<-pos (1/ ∣ p ∣) (positive⁻¹ ε) ⟩
      1/ ∣ p ∣ * ε  ∎

square : ℝ → ℝ
sequence (square x) = map (λ p → p * p) (sequence x)
isCauchy (square x) ε = B ℕ.⊔ proj₁ (isCauchy x (1/ (b ℚ.+ b) * ε)) , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (map (λ p → p * p) (sequence x)) m - lookup (map (λ p → p * p) (sequence x)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m _ (sequence x)) (lookup-map n _ (sequence x)) ⟩
  ∣ lookup (sequence x) m * lookup (sequence x) m - lookup (sequence x) n * lookup (sequence x) n ∣
    ≡⟨ cong ∣_∣ (lemma (lookup (sequence x) m) (lookup (sequence x) n)) ⟩
  ∣ (lookup (sequence x) m ℚ.+ lookup (sequence x) n) * (lookup (sequence x) m - lookup (sequence x) n) ∣
    ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (lookup (sequence x) m ℚ.+ lookup (sequence x) n) (lookup (sequence x) m - lookup (sequence x) n) ⟩
  ∣ lookup (sequence x) m ℚ.+ lookup (sequence x) n ∣ * ∣ lookup (sequence x) m - lookup (sequence x) n ∣
    ≤⟨ *-monoʳ-≤-nonNeg ∣ lookup (sequence x) m - lookup (sequence x) n ∣ {{∣-∣-nonNeg (lookup (sequence x) m - lookup (sequence x) n)}} (∣p+q∣≤∣p∣+∣q∣ (lookup (sequence x) m) (lookup (sequence x) n)) ⟩
  (∣ lookup (sequence x) m ∣ ℚ.+ ∣ lookup (sequence x) n ∣) * ∣ lookup (sequence x) m - lookup (sequence x) n ∣
    ≤⟨ *-monoʳ-≤-nonNeg ∣ lookup (sequence x) m - lookup (sequence x) n ∣ {{∣-∣-nonNeg (lookup (sequence x) m - lookup (sequence x) n)}} (<⇒≤ (+-mono-<
      (b-prop (ℕ.≤-trans (ℕ.m≤m⊔n B (proj₁ (isCauchy x (1/ (b ℚ.+ b) * ε)))) m≥N))
      (b-prop (ℕ.≤-trans (ℕ.m≤m⊔n B (proj₁ (isCauchy x (1/ (b ℚ.+ b) * ε)))) n≥N))
    )) ⟩
  (b ℚ.+ b) * ∣ lookup (sequence x) m - lookup (sequence x) n ∣
    <⟨ *-monoʳ-<-pos (b ℚ.+ b) (proj₂ (isCauchy x (1/ (b ℚ.+ b) * ε))
      (ℕ.≤-trans (ℕ.m≤n⊔m B (proj₁ (isCauchy x (1/ (b ℚ.+ b) * ε)))) m≥N)
      (ℕ.≤-trans (ℕ.m≤n⊔m B (proj₁ (isCauchy x (1/ (b ℚ.+ b) * ε)))) n≥N)
    ) ⟩
  (b ℚ.+ b) * (1/ (b ℚ.+ b) * ε)
    ≡˘⟨ *-assoc (b ℚ.+ b) (1/ (b ℚ.+ b)) ε ⟩
  ((b ℚ.+ b) * 1/ (b ℚ.+ b)) * ε
    ≡⟨ cong (_* ε) (*-inverseʳ (b ℚ.+ b)) ⟩
  1ℚ * ε
    ≡⟨ *-identityˡ ε ⟩
  ε ∎
  where
    open ≤-Reasoning

    B : ℕ.ℕ
    B = proj₁ (isCauchy x 1ℚ)

    b : ℚ
    b = 1ℚ ℚ.+ ∣ lookup (sequence x) B ∣

    instance _ : Positive b
    _ = positive $ begin-strict
      0ℚ                               ≤⟨ 0≤∣p∣ (lookup (sequence x) B) ⟩
      ∣ lookup (sequence x) B ∣        ≡˘⟨ +-identityˡ ∣ lookup (sequence x) B ∣ ⟩
      0ℚ ℚ.+ ∣ lookup (sequence x) B ∣ <⟨ +-monoˡ-< ∣ lookup (sequence x) B ∣ {0ℚ} {1ℚ} (*<* (+<+ (s≤s z≤n))) ⟩
      1ℚ ℚ.+ ∣ lookup (sequence x) B ∣ ≡⟨⟩
      b                                ∎

    instance _ : NonZero b
    _ = pos⇒nonZero b

    instance _ : Positive (b ℚ.+ b)
    _ = positive $ begin-strict
      0ℚ        ≡⟨⟩
      0ℚ ℚ.+ 0ℚ <⟨ +-mono-< (positive⁻¹ b) (positive⁻¹ b) ⟩
      b ℚ.+ b   ∎

    instance _ : NonZero (b ℚ.+ b)
    _ = pos⇒nonZero (b ℚ.+ b)

    instance _ : Positive (1/ (b ℚ.+ b) * ε)
    _ = positive $ begin-strict
      0ℚ               ≡⟨⟩
      0ℚ * 0ℚ          ≡˘⟨ *-zeroˡ ε ⟩
      0ℚ * ε           <⟨ *-monoˡ-<-pos ε (positive⁻¹ (1/ (b ℚ.+ b)) {{1/pos⇒pos (b ℚ.+ b)}}) ⟩
      1/ (b ℚ.+ b) * ε ∎

    b-prop : ∀ {n} → n ℕ.≥ B → ∣ lookup (sequence x) n ∣ < b
    b-prop {n} n≥B = begin-strict
     ∣ lookup (sequence x) n ∣ ≡˘⟨ cong ∣_∣ (+-identityʳ (lookup (sequence x) n)) ⟩
     ∣ lookup (sequence x) n ℚ.+ 0ℚ ∣ ≡˘⟨ cong (λ # → ∣ lookup (sequence x) n ℚ.+ # ∣) (+-inverseˡ (lookup (sequence x) B)) ⟩
     ∣ lookup (sequence x) n ℚ.+ (- lookup (sequence x) B ℚ.+ lookup (sequence x) B) ∣ ≡˘⟨ cong ∣_∣ (+-assoc (lookup (sequence x) n) (- lookup (sequence x) B) (lookup (sequence x) B)) ⟩
     ∣ (lookup (sequence x) n - lookup (sequence x) B) ℚ.+ lookup (sequence x) B ∣ ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (lookup (sequence x) n - lookup (sequence x) B) (lookup (sequence x) B) ⟩
     ∣ lookup (sequence x) n - lookup (sequence x) B ∣ ℚ.+ ∣ lookup (sequence x) B ∣ <⟨ +-monoˡ-< ∣ lookup (sequence x) B ∣ (proj₂ (isCauchy x 1ℚ) n≥B ℕ.≤-refl) ⟩
     1ℚ ℚ.+ ∣ lookup (sequence x) B ∣ ≡⟨⟩
     b ∎

    lemma : ∀ a b → a * a - b * b ≡ (a ℚ.+ b) * (a - b)
    lemma = solve 2 (λ a b → (a :* a :- b :* b) , ((a :+ b) :* (a :- b))) refl
      where open +-*-Solver

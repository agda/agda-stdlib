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
open import Data.Rational.Base as ℚ hiding (_+_; -_; _*_)
open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Unnormalised using (*<*)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary

open import Function.Metric.Rational.CauchySequence d-metric public renaming (CauchySequence to ℝ)

fromℚ : ℚ → ℝ
fromℚ = embed

0ℝ : ℝ
0ℝ = fromℚ 0ℚ

_+_ : ℝ → ℝ → ℝ
sequence (x + y) = zipWith ℚ._+_ (sequence x) (sequence y)
isCauchy (x + y) ε = proj₁ [x] ℕ.+ proj₁ [y] , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (zipWith ℚ._+_ (sequence x) (sequence y)) m - lookup (zipWith ℚ._+_ (sequence x) (sequence y)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣)
      (lookup-zipWith m ℚ._+_ (sequence x) (sequence y))
      (lookup-zipWith n ℚ._+_ (sequence x) (sequence y))
    ⟩
  ∣ (lookup (sequence x) m ℚ.+ lookup (sequence y) m) - (x ‼ n ℚ.+ y ‼ n) ∣
    ≡⟨ cong ∣_∣ (lemma (lookup (sequence x) m) (lookup (sequence y) m) (x ‼ n) (y ‼ n)) ⟩
  ∣ (lookup (sequence x) m - x ‼ n) ℚ.+ (lookup (sequence y) m - y ‼ n) ∣
    ≤⟨ ∣p+q∣≤∣p∣+∣q∣
      (lookup (sequence x) m - x ‼ n)
      (lookup (sequence y) m - y ‼ n)
    ⟩
  ∣ lookup (sequence x) m - x ‼ n ∣ ℚ.+ ∣ lookup (sequence y) m - y ‼ n ∣
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
  ½ ℚ.* ε ℚ.+ ½ ℚ.* ε
    ≡⟨ *-distribʳ-+ ε ½ ½ ⟨
  1ℚ ℚ.* ε
    ≡⟨ *-identityˡ ε ⟩
  ε ∎
  where
    open ≤-Reasoning
    instance _ : Positive (½ ℚ.* ε)
    _ = pos*pos⇒pos ½ ε
    [x] = isCauchy x (½ ℚ.* ε)
    [y] = isCauchy y (½ ℚ.* ε)

    lemma : ∀ a b c d → (a ℚ.+ b) - (c ℚ.+ d) ≡ (a - c) ℚ.+ (b - d)
    lemma = solve 4 (λ a b c d → ((a :+ b) :- (c :+ d)) , ((a :- c) :+ (b :- d))) refl
      where open +-*-Solver

-_ : ℝ → ℝ
sequence (- x) = map ℚ.-_ (sequence x)
isCauchy (- x) ε = proj₁ (isCauchy x ε) , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (map ℚ.-_ (sequence x)) m - lookup (map ℚ.-_ (sequence x)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m ℚ.-_ (sequence x)) (lookup-map n ℚ.-_ (sequence x)) ⟩
  ∣ ℚ.- lookup (sequence x) m - ℚ.- x ‼ n ∣
    ≡⟨ cong ∣_∣ (lemma (lookup (sequence x) m) (x ‼ n)) ⟩
  ∣ ℚ.- (lookup (sequence x) m - x ‼ n) ∣
    ≡⟨ ∣-p∣≡∣p∣ (lookup (sequence x) m - x ‼ n) ⟩
  ∣ lookup (sequence x) m - x ‼ n ∣
    <⟨ proj₂ (isCauchy x ε) m≥N n≥N ⟩
  ε ∎
  where
    open ≤-Reasoning
    lemma : ∀ a b → ℚ.- a - ℚ.- b ≡ ℚ.- (a - b)
    lemma = solve 2 (λ a b → (:- a) :- (:- b) , (:- (a :- b))) refl
      where open +-*-Solver

_*ₗ_ : ℚ → ℝ → ℝ
sequence (p *ₗ x) = map (p ℚ.*_) (sequence x)
isCauchy (p *ₗ x) ε with p ≟ 0ℚ
... | yes p≡0 = 0 , λ {m} {n} _ _ → begin-strict
  ∣ lookup (map (p ℚ.*_) (sequence x)) m - lookup (map (p ℚ.*_) (sequence x)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m (p ℚ.*_) (sequence x)) (lookup-map n (p ℚ.*_) (sequence x)) ⟩
  ∣ p ℚ.* lookup (sequence x) m - p ℚ.* x ‼ n ∣
    ≡⟨ cong (λ # → ∣ p ℚ.* lookup (sequence x) m ℚ.+ # ∣) (neg-distribʳ-* p (x ‼ n)) ⟩
  ∣ p ℚ.* lookup (sequence x) m ℚ.+ p ℚ.* ℚ.- x ‼ n ∣
    ≡⟨ cong ∣_∣ (*-distribˡ-+ p (lookup (sequence x) m) (ℚ.- x ‼ n)) ⟨
  ∣ p ℚ.* (lookup (sequence x) m - x ‼ n) ∣
    ≡⟨ cong (λ # → ∣ # ℚ.* (lookup (sequence x) m - x ‼ n) ∣) p≡0 ⟩
  ∣ 0ℚ ℚ.* (lookup (sequence x) m - x ‼ n) ∣
    ≡⟨ cong ∣_∣ (*-zeroˡ (lookup (sequence x) m - x ‼ n)) ⟩
  ∣ 0ℚ ∣
    ≡⟨⟩
  0ℚ
    <⟨ positive⁻¹ ε ⟩
  ε ∎
  where open ≤-Reasoning
... | no  p≢0 = proj₁ (isCauchy x (1/ ∣ p ∣ ℚ.* ε)) , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (map (p ℚ.*_) (sequence x)) m - lookup (map (p ℚ.*_) (sequence x)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m (p ℚ.*_) (sequence x)) (lookup-map n (p ℚ.*_) (sequence x)) ⟩
  ∣ p ℚ.* lookup (sequence x) m - p ℚ.* x ‼ n ∣
    ≡⟨ cong (λ # → ∣ p ℚ.* lookup (sequence x) m ℚ.+ # ∣) (neg-distribʳ-* p (x ‼ n)) ⟩
  ∣ p ℚ.* lookup (sequence x) m ℚ.+ p ℚ.* ℚ.- x ‼ n ∣
    ≡⟨ cong ∣_∣ (*-distribˡ-+ p (lookup (sequence x) m) (ℚ.- x ‼ n)) ⟨
  ∣ p ℚ.* (lookup (sequence x) m - x ‼ n) ∣
    ≡⟨ ∣p*q∣≡∣p∣*∣q∣ p (lookup (sequence x) m - x ‼ n) ⟩
  ∣ p ∣ ℚ.* ∣ lookup (sequence x) m - x ‼ n ∣
    <⟨ *-monoʳ-<-pos ∣ p ∣ (proj₂ (isCauchy x (1/ ∣ p ∣ ℚ.* ε)) m≥N n≥N) ⟩
  ∣ p ∣ ℚ.* (1/ ∣ p ∣ ℚ.* ε)
    ≡⟨ *-assoc ∣ p ∣ (1/ ∣ p ∣) ε ⟨
  (∣ p ∣ ℚ.* 1/ ∣ p ∣) ℚ.* ε
    ≡⟨ cong (ℚ._* ε) (*-inverseʳ ∣ p ∣) ⟩
  1ℚ ℚ.* ε
    ≡⟨ *-identityˡ ε ⟩
  ε ∎
  where
    open ≤-Reasoning
    instance _ : NonZero ∣ p ∣
    _ = ≢-nonZero {∣ p ∣} λ ∣p∣≡0 → p≢0 (∣p∣≡0⇒p≡0 p ∣p∣≡0)
    instance _ : Positive ∣ p ∣
    _ = nonNeg∧nonZero⇒pos ∣ p ∣ {{∣-∣-nonNeg p}}
    instance _ : Positive (1/ ∣ p ∣)
    _ = 1/pos⇒pos ∣ p ∣
    instance _ : Positive (1/ ∣ p ∣ ℚ.* ε)
    _ = pos*pos⇒pos (1/ ∣ p ∣) ε

square : ℝ → ℝ
sequence (square x) = map (λ p → p ℚ.* p) (sequence x)
isCauchy (square x) ε = B ℕ.⊔ proj₁ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε)) , λ {m} {n} m≥N n≥N → begin-strict
  ∣ lookup (map (λ p → p ℚ.* p) (sequence x)) m - lookup (map (λ p → p ℚ.* p) (sequence x)) n ∣
    ≡⟨ cong₂ (λ a b → ∣ a - b ∣) (lookup-map m _ (sequence x)) (lookup-map n _ (sequence x)) ⟩
  ∣ lookup (sequence x) m ℚ.* lookup (sequence x) m - x ‼ n ℚ.* x ‼ n ∣
    ≡⟨ cong ∣_∣ (lemma (lookup (sequence x) m) (x ‼ n)) ⟩
  ∣ (lookup (sequence x) m ℚ.+ x ‼ n) ℚ.* (lookup (sequence x) m - x ‼ n) ∣
    ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (lookup (sequence x) m ℚ.+ x ‼ n) (lookup (sequence x) m - x ‼ n) ⟩
  ∣ lookup (sequence x) m ℚ.+ x ‼ n ∣ ℚ.* ∣ lookup (sequence x) m - x ‼ n ∣
    ≤⟨ *-monoʳ-≤-nonNeg ∣ lookup (sequence x) m - x ‼ n ∣
      {{∣-∣-nonNeg (lookup (sequence x) m - x ‼ n)}}
      (∣p+q∣≤∣p∣+∣q∣ (lookup (sequence x) m) (x ‼ n))
    ⟩
  (∣ lookup (sequence x) m ∣ ℚ.+ ∣ x ‼ n ∣) ℚ.* ∣ lookup (sequence x) m - x ‼ n ∣
    ≤⟨ *-monoʳ-≤-nonNeg ∣ lookup (sequence x) m - x ‼ n ∣
      {{∣-∣-nonNeg (lookup (sequence x) m - x ‼ n)}}
      (<⇒≤ (+-mono-<
        (b-prop (ℕ.≤-trans (ℕ.m≤m⊔n B (proj₁ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε)))) m≥N))
        (b-prop (ℕ.≤-trans (ℕ.m≤m⊔n B (proj₁ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε)))) n≥N))
      ))
    ⟩
  (b ℚ.+ b) ℚ.* ∣ lookup (sequence x) m - x ‼ n ∣
    <⟨ *-monoʳ-<-pos (b ℚ.+ b) (proj₂ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε))
      (ℕ.≤-trans (ℕ.m≤n⊔m B (proj₁ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε)))) m≥N)
      (ℕ.≤-trans (ℕ.m≤n⊔m B (proj₁ (isCauchy x (1/ (b ℚ.+ b) ℚ.* ε)))) n≥N)
    ) ⟩
  (b ℚ.+ b) ℚ.* (1/ (b ℚ.+ b) ℚ.* ε)
    ≡⟨ *-assoc (b ℚ.+ b) (1/ (b ℚ.+ b)) ε ⟨
  ((b ℚ.+ b) ℚ.* 1/ (b ℚ.+ b)) ℚ.* ε
    ≡⟨ cong (ℚ._* ε) (*-inverseʳ (b ℚ.+ b)) ⟩
  1ℚ ℚ.* ε
    ≡⟨ *-identityˡ ε ⟩
  ε ∎
  where
    open ≤-Reasoning

    B : ℕ.ℕ
    B = proj₁ (isCauchy x 1ℚ)

    b : ℚ
    b = 1ℚ ℚ.+ ∣ lookup (sequence x) B ∣

    instance _ : Positive b
    _ = pos+nonNeg⇒pos 1ℚ ∣ lookup (sequence x) B ∣ {{∣-∣-nonNeg (lookup (sequence x) B)}}

    instance _ : NonZero b
    _ = pos⇒nonZero b

    instance _ : Positive (b ℚ.+ b)
    _ = pos+pos⇒pos b b

    instance _ : NonZero (b ℚ.+ b)
    _ = pos⇒nonZero (b ℚ.+ b)

    instance _ : Positive (1/ (b ℚ.+ b) ℚ.* ε)
    _ = pos*pos⇒pos (1/ (b ℚ.+ b)) {{1/pos⇒pos (b ℚ.+ b)}} ε

    b-prop : ∀ {n} → n ℕ.≥ B → ∣ x ‼ n ∣ < b
    b-prop {n} n≥B = begin-strict
     ∣ x ‼ n ∣
       ≡⟨ cong ∣_∣ (+-identityʳ (x ‼ n)) ⟨
     ∣ x ‼ n ℚ.+ 0ℚ ∣
       ≡⟨ cong (λ # → ∣ x ‼ n ℚ.+ # ∣) (+-inverseˡ (lookup (sequence x) B)) ⟨
     ∣ x ‼ n ℚ.+ (ℚ.- lookup (sequence x) B ℚ.+ lookup (sequence x) B) ∣
       ≡⟨ cong ∣_∣ (+-assoc (x ‼ n) (ℚ.- lookup (sequence x) B) (lookup (sequence x) B)) ⟨
     ∣ (x ‼ n - lookup (sequence x) B) ℚ.+ lookup (sequence x) B ∣
       ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (x ‼ n - lookup (sequence x) B) (lookup (sequence x) B) ⟩
     ∣ x ‼ n - lookup (sequence x) B ∣ ℚ.+ ∣ lookup (sequence x) B ∣
       <⟨ +-monoˡ-< ∣ lookup (sequence x) B ∣ (proj₂ (isCauchy x 1ℚ) n≥B ℕ.≤-refl) ⟩
     1ℚ ℚ.+ ∣ lookup (sequence x) B ∣ ≡⟨⟩
     b ∎

    lemma : ∀ a b → a ℚ.* a - b ℚ.* b ≡ (a ℚ.+ b) ℚ.* (a - b)
    lemma = solve 2 (λ a b → (a :* a :- b :* b) , ((a :+ b) :* (a :- b))) refl
      where open +-*-Solver

_*_ : ℝ → ℝ → ℝ
a * b = square (a + b) + ((- square a) + (- square b))

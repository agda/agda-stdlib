------------------------------------------------------------------------
-- The Agda standard library
--
-- Cauchy sequences on a metric over the rationals
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

open import Function.Metric.Rational.Bundles

module Function.Metric.Rational.CauchySequence {a ℓ} (M : Metric a ℓ) where

open Metric M hiding (_≈_)

open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base using (+<+)
open import Data.Product.Base
open import Data.Rational.Base
open import Data.Rational.Properties
open import Function.Base
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (cong₂)

record CauchySequence : Set a where
  field
    sequence : Stream Carrier
    isCauchy : ∀ ε → .{{Positive ε}} → Σ[ N ∈ ℕ ] ∀ {m n} → m ℕ.≥ N → n ℕ.≥ N → d (lookup sequence m) (lookup sequence n) < ε

open CauchySequence public

_≈_ : Rel CauchySequence zero
x ≈ y = ∀ ε → .{{Positive ε}} → Σ[ N ∈ ℕ ] (∀ {n} → n ℕ.≥ N → d (lookup (sequence x) n) (lookup (sequence y) n) < ε)

≈-refl : Reflexive _≈_
≈-refl {x} ε = 0 , λ {n} _ → begin-strict
  d (lookup (sequence x) n) (lookup (sequence x) n) ≡⟨ ≈⇒0 EqC.refl ⟩
  0ℚ                                                <⟨ positive⁻¹ ε ⟩
  ε                                                 ∎
  where open ≤-Reasoning

≈-sym : Symmetric _≈_
≈-sym {x} {y} p ε = proj₁ (p ε) , λ {n} n≥N → begin-strict
  d (lookup (sequence y) n) (lookup (sequence x) n) ≡⟨ sym (lookup (sequence y) n) (lookup (sequence x) n) ⟩
  d (lookup (sequence x) n) (lookup (sequence y) n) <⟨ proj₂ (p ε) n≥N ⟩
  ε                                                 ∎
  where open ≤-Reasoning

≈-trans : Transitive _≈_
≈-trans {x} {y} {z} p q ε = proj₁ (p (½ * ε)) ℕ.⊔ proj₁ (q (½ * ε)) , λ {n} n≥N → begin-strict
  d (lookup (sequence x) n) (lookup (sequence z) n)
    ≤⟨ triangle (lookup (sequence x) n) (lookup (sequence y) n) (lookup (sequence z) n) ⟩
  d (lookup (sequence x) n) (lookup (sequence y) n) + d (lookup (sequence y) n) (lookup (sequence z) n)
    <⟨ +-mono-<
      (proj₂ (p (½ * ε)) (ℕ.≤-trans (ℕ.m≤m⊔n (proj₁ (p (½ * ε))) (proj₁ (q (½ * ε)))) n≥N))
      (proj₂ (q (½ * ε)) (ℕ.≤-trans (ℕ.m≤n⊔m (proj₁ (p (½ * ε))) (proj₁ (q (½ * ε)))) n≥N))
    ⟩
  ½ * ε + ½ * ε
    ≡˘⟨ *-distribʳ-+ ε ½ ½ ⟩
  1ℚ * ε
    ≡⟨ *-identityˡ ε ⟩
  ε
    ∎
  where
    open ≤-Reasoning
    instance _ : Positive (½ * ε)
    _ = pos*pos⇒pos ½ ε

embed : Carrier → CauchySequence
embed x = record
  { sequence = repeat x
  ; isCauchy = λ ε → 0 , λ {m n} _ _ → begin-strict
    d (lookup (repeat x) m) (lookup (repeat x) n) ≡⟨ cong₂ d (lookup-repeat m x) (lookup-repeat n x) ⟩
    d x x                                         ≡⟨ ≈⇒0 EqC.refl ⟩
    0ℚ                                            <⟨ positive⁻¹ ε ⟩
    ε                                             ∎
  } where open ≤-Reasoning

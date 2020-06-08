------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unnormalized Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Unnormalised.Properties where

open import Algebra
import Algebra.Consequences.Setoid as FC
open import Algebra.Consequences.Propositional
open import Data.Nat.Base as ℕ using (suc; pred)
import Data.Nat.Properties as ℕ
open import Data.Nat.Solver renaming (module +-*-Solver to ℕ-solver)
open import Data.Integer.Base as ℤ using (ℤ; +0; +[1+_]; -[1+_]; 0ℤ; 1ℤ; -1ℤ)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤ-solver)
import Data.Integer.Properties as ℤ
import Data.Integer.Properties
open import Data.Rational.Unnormalised.Base
open import Data.Product using (_,_)
open import Data.Sum.Base using ([_,_]′; inj₁; inj₂)
open import Function.Base using (_on_; _$_; _∘_)
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Algebra.Properties.CommutativeSemigroup ℤ.*-commutativeSemigroup

------------------------------------------------------------------------
-- Properties of ↥_ and ↧_
------------------------------------------------------------------------

↥↧≡⇒≡ : ∀ {p q} → ↥ p ≡ ↥ q → ↧ₙ p ≡ ↧ₙ q → p ≡ q
↥↧≡⇒≡ refl refl = refl

------------------------------------------------------------------------
-- Properties of Positive/Negative/NonPositive/NonNegative predicates
------------------------------------------------------------------------

positive⇒nonNegative : ∀ {q} → Positive q → NonNegative q
positive⇒nonNegative {mkℚᵘ +0       _} _ = _
positive⇒nonNegative {mkℚᵘ +[1+ n ] _} _ = _

negative⇒nonPositive : ∀ {q} → Negative q → NonPositive q
negative⇒nonPositive {mkℚᵘ +0       _} _ = _
negative⇒nonPositive {mkℚᵘ -[1+ n ] _} _ = _

------------------------------------------------------------------------
-- Properties of _≃_
------------------------------------------------------------------------

drop-*≡* : ∀ {p q} → p ≃ q → ↥ p ℤ.* ↧ q ≡ ↥ q ℤ.* ↧ p
drop-*≡* (*≡* eq) = eq

≃-refl : Reflexive _≃_
≃-refl = *≡* refl

≃-reflexive : _≡_ ⇒ _≃_
≃-reflexive refl = *≡* refl

≃-sym : Symmetric _≃_
≃-sym (*≡* eq) = *≡* (sym eq)

≃-trans : Transitive _≃_
≃-trans {x} {y} {z} (*≡* ad≡cb) (*≡* cf≡ed) =
  *≡* (ℤ.*-cancelʳ-≡ (↥ x ℤ.* ↧ z) (↥ z ℤ.* ↧ x) (↧ y) (λ()) (begin
     ↥ x ℤ.* ↧ z ℤ.* ↧ y ≡⟨ xy∙z≈xz∙y (↥ x) _ _ ⟩
     ↥ x ℤ.* ↧ y ℤ.* ↧ z ≡⟨ cong (ℤ._* ↧ z) ad≡cb ⟩
     ↥ y ℤ.* ↧ x ℤ.* ↧ z ≡⟨ xy∙z≈xz∙y (↥ y) _ _ ⟩
     ↥ y ℤ.* ↧ z ℤ.* ↧ x ≡⟨ cong (ℤ._* ↧ x) cf≡ed ⟩
     ↥ z ℤ.* ↧ y ℤ.* ↧ x ≡⟨ xy∙z≈xz∙y (↥ z) _ _ ⟩
     ↥ z ℤ.* ↧ x ℤ.* ↧ y ∎))
  where open ≡-Reasoning

_≃?_ : Decidable _≃_
p ≃? q = Dec.map′ *≡* drop-*≡* (↥ p ℤ.* ↧ q ℤ.≟ ↥ q ℤ.* ↧ p)

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record
  { refl  = ≃-refl
  ; sym   = ≃-sym
  ; trans = ≃-trans
  }

≃-isDecEquivalence : IsDecEquivalence _≃_
≃-isDecEquivalence = record
  { isEquivalence = ≃-isEquivalence
  ; _≟_           = _≃?_
  }

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid = record
  { isEquivalence = ≃-isEquivalence
  }

≃-decSetoid : DecSetoid 0ℓ 0ℓ
≃-decSetoid = record
  { isDecEquivalence = ≃-isDecEquivalence
  }

------------------------------------------------------------------------
-- Properties of -_
------------------------------------------------------------------------

neg-involutive-≡ : Involutive _≡_ (-_)
neg-involutive-≡ (mkℚᵘ n d) = cong (λ n → mkℚᵘ n d) (ℤ.neg-involutive n)

neg-involutive : Involutive _≃_ (-_)
neg-involutive p rewrite neg-involutive-≡ p = ≃-refl

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {p} {q} (*≡* p≡q) = *≡* $ begin
  ↥(- p) ℤ.* ↧ q            ≡˘⟨ ℤ.*-identityˡ (ℤ.-(↥ p) ℤ.* ↧ q) ⟩
  1ℤ ℤ.* (↥(- p) ℤ.* ↧ q)   ≡˘⟨ ℤ.*-assoc 1ℤ (↥(- p)) (↧ q) ⟩
  (1ℤ ℤ.* ℤ.-(↥ p)) ℤ.* ↧ q ≡˘⟨ cong (ℤ._* ↧ q) (ℤ.neg-distribʳ-* 1ℤ (↥ p)) ⟩
  ℤ.-(1ℤ ℤ.* ↥ p) ℤ.* ↧ q   ≡⟨ cong (ℤ._* ↧ q) (ℤ.neg-distribˡ-* 1ℤ (↥ p)) ⟩
  (-1ℤ ℤ.* ↥ p) ℤ.* ↧ q     ≡⟨ ℤ.*-assoc (ℤ.- 1ℤ) (↥ p) (↧ q) ⟩
  -1ℤ ℤ.* (↥ p ℤ.* ↧ q)     ≡⟨ cong (λ r → ℤ.- 1ℤ ℤ.* r) p≡q ⟩
  -1ℤ ℤ.* (↥ q ℤ.* ↧ p)     ≡˘⟨ ℤ.*-assoc (ℤ.- 1ℤ) (↥ q) (↧ p) ⟩
  (-1ℤ ℤ.* ↥ q) ℤ.* ↧ p     ≡˘⟨ cong (ℤ._* ↧ p) (ℤ.neg-distribˡ-* 1ℤ (↥ q)) ⟩
  ℤ.-(1ℤ ℤ.* ↥ q) ℤ.* ↧ p   ≡⟨ cong (ℤ._* ↧ p) (ℤ.neg-distribʳ-* 1ℤ (↥ q)) ⟩
  (1ℤ ℤ.* ↥(- q)) ℤ.* ↧ p   ≡⟨ ℤ.*-assoc 1ℤ (ℤ.-(↥ q)) (↧ p) ⟩
  1ℤ ℤ.* (↥(- q) ℤ.* ↧ p)   ≡⟨ ℤ.*-identityˡ (↥(- q) ℤ.* ↧ p) ⟩
  ↥(- q) ℤ.* ↧ p            ∎ where open ≡-Reasoning

neg-mono-<-> : -_ Preserves  _<_ ⟶ _>_
neg-mono-<-> {p} {q} (*<* p<q) = *<* $ begin-strict
  ℤ.-  ↥ q ℤ.* ↧ p    ≡˘⟨ ℤ.neg-distribˡ-* (↥ q) (↧ p) ⟩
  ℤ.- (↥ q ℤ.* ↧ p)   <⟨ ℤ.neg-mono-<-> p<q ⟩
  ℤ.- (↥ p ℤ.* ↧ q)   ≡⟨ ℤ.neg-distribˡ-* (↥ p) (↧ q) ⟩
  ↥ (- p) ℤ.* ↧ (- q) ∎ where open ℤ.≤-Reasoning

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------
-- Relational properties

drop-*≤* : ∀ {p q} → p ≤ q → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p)
drop-*≤* (*≤* pq≤qp) = pq≤qp

≤-reflexive : _≃_ ⇒ _≤_
≤-reflexive (*≡* eq) = *≤* (ℤ.≤-reflexive eq)

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive ≃-refl

≤-trans : Transitive _≤_
≤-trans {i = p@(mkℚᵘ n₁ d₁-1)} {j = q@(mkℚᵘ n₂ d₂-1)} {k = r@(mkℚᵘ n₃ d₃-1)} (*≤* eq₁) (*≤* eq₂)
  = let d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r in *≤* $
  ℤ.*-cancelʳ-≤-pos (n₁ ℤ.* d₃) (n₃ ℤ.* d₁) d₂-1 $ begin
  (n₁  ℤ.* d₃) ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁   ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁   ℤ.* (d₂ ℤ.* d₃) ≡⟨ sym (ℤ.*-assoc n₁ d₂ d₃) ⟩
  (n₁  ℤ.* d₂) ℤ.* d₃  ≤⟨ ℤ.*-monoʳ-≤-pos d₃-1 eq₁ ⟩
  (n₂  ℤ.* d₁) ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  (d₁ ℤ.* n₂)  ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁  ℤ.* (n₂  ℤ.* d₃) ≤⟨ ℤ.*-monoˡ-≤-pos d₁-1 eq₂ ⟩
  d₁  ℤ.* (n₃  ℤ.* d₂) ≡⟨ sym (ℤ.*-assoc d₁ n₃ d₂) ⟩
  (d₁ ℤ.* n₃)  ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  (n₃  ℤ.* d₁) ℤ.* d₂  ∎ where open ℤ.≤-Reasoning

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = *≡* (ℤ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q = [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′ (ℤ.≤-total
  (↥ p ℤ.* ↧ q)
  (↥ q ℤ.* ↧ p))

infix 4 _≤?_
_≤?_ : Decidable _≤_
p ≤? q = Dec.map′ *≤* drop-*≤* (↥ p ℤ.* ↧ q ℤ.≤? ↥ q ℤ.* ↧ p)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant (*≤* p≤q₁) (*≤* p≤q₂) = cong *≤* (ℤ.≤-irrelevant p≤q₁ p≤q₂)

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≃_ _≤_
≤-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≃_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≃_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≃_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≃?_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Bundles

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ
≤-totalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

drop-*<* : ∀ {p q} → p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
drop-*<* (*<* pq<qp) = pq<qp

------------------------------------------------------------------------
-- Relationship between other operators

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (*<* x<y) refl = ℤ.<⇒≢ x<y refl

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (*<* x<y) = ℤ.<⇒≱ x<y ∘ drop-*≤*

≰⇒> : _≰_ ⇒ _>_
≰⇒> p≰q = *<* (ℤ.≰⇒> (p≰q ∘ *≤*))

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ p≮q = *≤* (ℤ.≮⇒≥ (p≮q ∘ *<*))

------------------------------------------------------------------------
-- Relational properties

<-irrefl-≡ : Irreflexive _≡_ _<_
<-irrefl-≡ refl (*<* x<x) = ℤ.<-irrefl refl x<x

<-irrefl : Irreflexive _≃_ _<_
<-irrefl (*≡* x≡y) (*<* x<y) = ℤ.<-irrefl x≡y x<y

<-asym : Asymmetric _<_
<-asym (*<* x<y) = ℤ.<-asym x<y ∘ drop-*<*

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {p} {q} {r} (*≤* p≤q) (*<* q<r) = *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡˘⟨ ℤ.*-assoc n₁ d₂ d₃ ⟩
  n₁ ℤ.*  d₂ ℤ.* d₃  ≤⟨ ℤ.*-monoʳ-≤-pos (pred (↧ₙ r)) p≤q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  d₁ ℤ.*  n₂ ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁ ℤ.* (n₂ ℤ.* d₃) <⟨ ℤ.*-monoˡ-<-pos (pred (↧ₙ p)) q<r ⟩
  d₁ ℤ.* (n₃ ℤ.* d₂) ≡˘⟨ ℤ.*-assoc d₁ n₃ d₂ ⟩
  d₁ ℤ.*  n₃ ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r) = *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡˘⟨ ℤ.*-assoc n₁ d₂ d₃ ⟩
  n₁ ℤ.*  d₂ ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (pred (↧ₙ r)) p<q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  d₁ ℤ.*  n₂ ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
  d₁ ℤ.* (n₂ ℤ.* d₃) ≤⟨ ℤ.*-monoˡ-≤-pos (pred (↧ₙ p)) q≤r ⟩
  d₁ ℤ.* (n₃ ℤ.* d₂) ≡˘⟨ ℤ.*-assoc d₁ n₃ d₂ ⟩
  d₁ ℤ.*  n₃ ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-trans : Transitive _<_
<-trans = ≤-<-trans ∘ <⇒≤

<-cmp : Trichotomous _≃_ _<_
<-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< x<y x≉y x≯y = tri< (*<* x<y) (x≉y ∘ drop-*≡*) (x≯y ∘ drop-*<*)
... | tri≈ x≮y x≈y x≯y = tri≈ (x≮y ∘ drop-*<*) (*≡* x≈y) (x≯y ∘ drop-*<*)
... | tri> x≮y x≉y x>y = tri> (x≮y ∘ drop-*<*) (x≉y ∘ drop-*≡*) (*<* x>y)

infix 4 _<?_
_<?_ : Decidable _<_
p <? q = Dec.map′ *<* drop-*<* (↥ p ℤ.* ↧ q ℤ.<? ↥ q ℤ.* ↧ p)

<-irrelevant : Irrelevant _<_
<-irrelevant (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤ.<-irrelevant p<q₁ p<q₂)

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ {p} {q} {r} (*≡* q≡r) (*<* p<q) = *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  n₁ ℤ.*  d₃ ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
  n₁ ℤ.* (d₃ ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
  n₁ ℤ.* (d₂ ℤ.* d₃) ≡˘⟨ ℤ.*-assoc n₁ d₂ d₃ ⟩
  n₁ ℤ.*  d₂ ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (pred (↧ₙ r)) p<q ⟩
  n₂ ℤ.*  d₁ ℤ.* d₃  ≡⟨ ℤ.*-assoc n₂ d₁ d₃ ⟩
  n₂ ℤ.* (d₁ ℤ.* d₃) ≡⟨ cong (n₂ ℤ.*_) (ℤ.*-comm d₁ d₃) ⟩
  n₂ ℤ.* (d₃ ℤ.* d₁) ≡˘⟨ ℤ.*-assoc n₂ d₃ d₁ ⟩
  n₂ ℤ.*  d₃ ℤ.* d₁  ≡⟨ cong (ℤ._* d₁) q≡r ⟩
  n₃ ℤ.*  d₂ ℤ.* d₁  ≡⟨ ℤ.*-assoc n₃ d₂ d₁ ⟩
  n₃ ℤ.* (d₂ ℤ.* d₁) ≡⟨ cong (n₃ ℤ.*_) (ℤ.*-comm d₂ d₁) ⟩
  n₃ ℤ.* (d₁ ℤ.* d₂) ≡˘⟨ ℤ.*-assoc n₃ d₁ d₂ ⟩
  n₃ ℤ.*  d₁ ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning
        n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ q≃r q<p
  = subst (_< _) (neg-involutive-≡ _)
  $ subst (_ <_) (neg-involutive-≡ _)
  $ neg-mono-<-> (<-respʳ-≃ (-‿cong q≃r) (neg-mono-<-> q<p))

<-resp-≃ : _<_ Respects₂ _≃_
<-resp-≃ = <-respʳ-≃ , <-respˡ-≃

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder-≡ : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder-≡ = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl-≡
  ; trans         = <-trans
  ; <-resp-≈      = subst (_ <_) , subst (_< _)
  }

<-isStrictPartialOrder : IsStrictPartialOrder _≃_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≃-isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp-≃
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≃_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = ≃-isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder-≡ : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder-≡ = record
  { isStrictPartialOrder = <-isStrictPartialOrder-≡
  }

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≃
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public

------------------------------------------------------------------------
-- Properties of ↥_/↧_

≥0⇒↥≥0 : ∀ {n dm} → mkℚᵘ n dm ≥ 0ℚᵘ → n ℤ.≥ 0ℤ
≥0⇒↥≥0 {n} {dm} r≥0 = ℤ.≤-trans (drop-*≤* r≥0)
                                (ℤ.≤-reflexive $ ℤ.*-identityʳ n)

>0⇒↥>0 : ∀ {n dm} → mkℚᵘ n dm > 0ℚᵘ → n ℤ.> 0ℤ
>0⇒↥>0 {n} {dm} r>0 = ℤ.<-≤-trans (drop-*<* r>0)
                                  (ℤ.≤-reflexive $ ℤ.*-identityʳ n)

------------------------------------------------------------------------
-- Properties of Positive/NonPositive/Negative/NonNegative and _≤_/_<_

positive⁻¹ : ∀ {q} → Positive q → q > 0ℚᵘ
positive⁻¹ {mkℚᵘ +[1+ n ] _} _ = *<* (ℤ.+<+ (ℕ.s≤s ℕ.z≤n))

nonNegative⁻¹ : ∀ {q} → NonNegative q → q ≥ 0ℚᵘ
nonNegative⁻¹ {mkℚᵘ +0       _} _ = *≤* (ℤ.+≤+ ℕ.z≤n)
nonNegative⁻¹ {mkℚᵘ +[1+ n ] _} _ = *≤* (ℤ.+≤+ ℕ.z≤n)

negative⁻¹ : ∀ {q} → Negative q → q < 0ℚᵘ
negative⁻¹ {mkℚᵘ -[1+ n ] _} _ = *<* ℤ.-<+

nonPositive⁻¹ : ∀ {q} → NonPositive q → q ≤ 0ℚᵘ
nonPositive⁻¹ {mkℚᵘ +0       _} _ = *≤* (ℤ.+≤+ ℕ.z≤n)
nonPositive⁻¹ {mkℚᵘ -[1+ n ] _} _ = *≤* ℤ.-≤+

negative<positive : ∀ {p q} → Negative p → Positive q → p < q
negative<positive p<0 q>0 = <-trans (negative⁻¹ p<0) (positive⁻¹ q>0)

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  }

+-rawMonoid : RawMonoid 0ℓ 0ℓ
+-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  ; ε   = 0ℚᵘ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { Carrier = ℚᵘ
  ; _≈_ = _≃_
  ; _∙_ = _+_
  ; ε = 0ℚᵘ
  ; _⁻¹ = -_
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { Carrier = ℚᵘ
  ; _≈_ = _≃_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0ℚᵘ
  ; 1# = 1ℚᵘ
  }

------------------------------------------------------------------------
-- Algebraic properties

-- Congruence

+-cong : Congruent₂ _≃_ _+_
+-cong {x} {y} {u} {v} (*≡* ab′∼a′b) (*≡* cd′∼c′d) = *≡* (begin
  (↥x ℤ.* ↧u ℤ.+ ↥u ℤ.* ↧x) ℤ.* (↧y ℤ.* ↧v)               ≡⟨ solve 6 (λ ↥x ↧x ↧y ↥u ↧u ↧v →
                                                             (↥x :* ↧u :+ ↥u :* ↧x) :* (↧y :* ↧v) :=
                                                             (↥x :* ↧y :* (↧u :* ↧v)) :+ ↥u :* ↧v :* (↧x :* ↧y))
                                                             refl (↥ x) (↧ x) (↧ y) (↥ u) (↧ u) (↧ v) ⟩
  ↥x ℤ.* ↧y ℤ.* (↧u ℤ.* ↧v) ℤ.+ ↥u ℤ.* ↧v ℤ.* (↧x ℤ.* ↧y) ≡⟨ cong₂ ℤ._+_ (cong (ℤ._* (↧u ℤ.* ↧v)) ab′∼a′b)
                                                                         (cong (ℤ._* (↧x ℤ.* ↧y)) cd′∼c′d) ⟩
  ↥y ℤ.* ↧x ℤ.* (↧u ℤ.* ↧v) ℤ.+ ↥v ℤ.* ↧u ℤ.* (↧x ℤ.* ↧y) ≡⟨ solve 6 (λ ↧x ↥y ↧y ↧u ↥v ↧v →
                                                             (↥y :* ↧x :* (↧u :* ↧v)) :+ ↥v :* ↧u :* (↧x :* ↧y) :=
                                                             (↥y :* ↧v :+ ↥v :* ↧y) :* (↧x :* ↧u))
                                                             refl (↧ x) (↥ y) (↧ y) (↧ u) (↥ v) (↧ v) ⟩
  (↥y ℤ.* ↧v ℤ.+ ↥v ℤ.* ↧y) ℤ.* (↧x ℤ.* ↧u)               ∎)
  where
  ↥x = ↥ x; ↧x = ↧ x; ↥y = ↥ y; ↧y = ↧ y; ↥u = ↥ u; ↧u = ↧ u; ↥v = ↥ v; ↧v = ↧ v
  open ≡-Reasoning
  open ℤ-solver

+-congʳ : ∀ p {q r} → q ≃ r → p + q ≃ p + r
+-congʳ p q≃r = +-cong (≃-refl {p}) q≃r

+-congˡ : ∀ p {q r} → q ≃ r → q + p ≃ r + p
+-congˡ p q≃r = +-cong q≃r (≃-refl {p})

-- Associativity

+-assoc-↥ : Associative (_≡_ on ↥_) _+_
+-assoc-↥ p q r = solve 6 (λ ↥p ↧p ↥q ↧q ↥r ↧r →
    (↥p :* ↧q :+ ↥q :* ↧p) :* ↧r :+ ↥r :* (↧p :* ↧q) :=
    ↥p :* (↧q :* ↧r) :+ (↥q :* ↧r :+ ↥r :* ↧q) :* ↧p)
  refl (↥ p) (↧ p) (↥ q) (↧ q) (↥ r) (↧ r)
  where open ℤ-solver

+-assoc-↧ : Associative (_≡_ on ↧ₙ_) _+_
+-assoc-↧ p q r = ℕ.*-assoc (↧ₙ p) (↧ₙ q) (↧ₙ r)

+-assoc-≡ : Associative _≡_ _+_
+-assoc-≡ p q r = ↥↧≡⇒≡ (+-assoc-↥ p q r) (+-assoc-↧ p q r)

+-assoc : Associative _≃_ _+_
+-assoc p q r = ≃-reflexive (+-assoc-≡ p q r)

-- Commutativity

+-comm-↥ : Commutative (_≡_ on ↥_) _+_
+-comm-↥ p q = ℤ.+-comm (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)

+-comm-↧ : Commutative (_≡_ on ↧ₙ_) _+_
+-comm-↧ p q = ℕ.*-comm (↧ₙ p) (↧ₙ q)

+-comm-≡ : Commutative _≡_ _+_
+-comm-≡ p q = ↥↧≡⇒≡ (+-comm-↥ p q) (+-comm-↧ p q)

+-comm : Commutative _≃_ _+_
+-comm p q = ≃-reflexive (+-comm-≡ p q)

-- Identities

+-identityˡ-↥ : LeftIdentity (_≡_ on ↥_) 0ℚᵘ _+_
+-identityˡ-↥ p = begin
  0ℤ ℤ.* ↧ p ℤ.+ ↥ p ℤ.* 1ℤ ≡⟨ cong₂ ℤ._+_ (ℤ.*-zeroˡ (↧ p)) (ℤ.*-identityʳ (↥ p)) ⟩
  0ℤ ℤ.+ ↥ p                ≡⟨ ℤ.+-identityˡ (↥ p) ⟩
  ↥ p                       ∎ where open ≡-Reasoning

+-identityˡ-↧ : LeftIdentity (_≡_ on ↧ₙ_) 0ℚᵘ _+_
+-identityˡ-↧ p = ℕ.+-identityʳ (↧ₙ p)

+-identityˡ-≡ : LeftIdentity _≡_ 0ℚᵘ _+_
+-identityˡ-≡ p = ↥↧≡⇒≡ (+-identityˡ-↥ p) (+-identityˡ-↧ p)

+-identityˡ : LeftIdentity _≃_ 0ℚᵘ _+_
+-identityˡ p = ≃-reflexive (+-identityˡ-≡ p)

+-identityʳ-≡ : RightIdentity _≡_ 0ℚᵘ _+_
+-identityʳ-≡ = comm+idˡ⇒idʳ +-comm-≡ {e = 0ℚᵘ} +-identityˡ-≡

+-identityʳ : RightIdentity _≃_ 0ℚᵘ _+_
+-identityʳ p = ≃-reflexive (+-identityʳ-≡ p)

+-identity-≡ : Identity _≡_ 0ℚᵘ _+_
+-identity-≡ = +-identityˡ-≡ , +-identityʳ-≡

+-identity : Identity _≃_ 0ℚᵘ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseˡ : LeftInverse _≃_ 0ℚᵘ -_ _+_
+-inverseˡ p = *≡* let n = ↥ p; d = ↧ p in
  ((ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d) ℤ.* 1ℤ ≡⟨ ℤ.*-identityʳ ((ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d) ⟩
  (ℤ.- n) ℤ.* d ℤ.+ n ℤ.* d          ≡˘⟨ cong (ℤ._+ (n ℤ.* d)) (ℤ.neg-distribˡ-* n d) ⟩
  ℤ.- (n ℤ.* d) ℤ.+ n ℤ.* d          ≡⟨ ℤ.+-inverseˡ (n ℤ.* d) ⟩
  0ℤ                                 ∎ where open ≡-Reasoning

+-inverseʳ : RightInverse _≃_ 0ℚᵘ -_ _+_
+-inverseʳ p = *≡* let n = ↥ p; d = ↧ p in
  (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ℤ.* 1ℤ ≡⟨ ℤ.*-identityʳ (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ⟩
  n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d          ≡˘⟨ cong (λ n+d → n ℤ.* d ℤ.+ n+d) (ℤ.neg-distribˡ-* n d) ⟩
  n ℤ.* d ℤ.+ ℤ.- (n ℤ.* d)          ≡⟨ ℤ.+-inverseʳ (n ℤ.* d) ⟩
  0ℤ                                 ∎ where open ≡-Reasoning

+-inverse : Inverse _≃_ 0ℚᵘ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

+-cancelˡ : ∀ {r p q} → r + p ≃ r + q → p ≃ q
+-cancelˡ {r} {p} {q} r+p≃r+q = begin-equality
  p            ≈˘⟨ +-identityʳ p ⟩
  p + 0ℚᵘ      ≈⟨ +-congʳ p (≃-sym (+-inverseʳ r)) ⟩
  p + (r - r)  ≈˘⟨ +-assoc p r (- r) ⟩
  (p + r) - r  ≈⟨ +-congˡ (- r) (+-comm p r) ⟩
  (r + p) - r  ≈⟨ +-congˡ (- r) r+p≃r+q ⟩
  (r + q) - r  ≈⟨ +-congˡ (- r) (+-comm r q) ⟩
  (q + r) - r  ≈⟨ +-assoc q r (- r) ⟩
  q + (r - r)  ≈⟨ +-congʳ q (+-inverseʳ r) ⟩
  q + 0ℚᵘ      ≈⟨ +-identityʳ q ⟩
  q            ∎ where open ≤-Reasoning

+-cancelʳ : ∀ {r p q} → p + r ≃ q + r → p ≃ q
+-cancelʳ {r} {p} {q} p+r≃q+r = +-cancelˡ {r} $ begin-equality
  r + p ≈⟨ +-comm r p ⟩
  p + r ≈⟨ p+r≃q+r ⟩
  q + r ≈⟨ +-comm q r ⟩
  r + q ∎ where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _+_ and -_

neg-distrib-+ : ∀ p q → - (p + q) ≡ (- p) + (- q)
neg-distrib-+ p q = ↥↧≡⇒≡ (begin
    ℤ.- (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p)       ≡⟨ ℤ.neg-distrib-+ (↥ p ℤ.* ↧ q) _ ⟩
    ℤ.- (↥ p ℤ.* ↧ q) ℤ.+ ℤ.- (↥ q ℤ.* ↧ p) ≡⟨ cong₂ ℤ._+_ (ℤ.neg-distribˡ-* (↥ p) _)
                                                           (ℤ.neg-distribˡ-* (↥ q) _) ⟩
    (ℤ.- ↥ p) ℤ.* ↧ q ℤ.+ (ℤ.- ↥ q) ℤ.* ↧ p ∎
  ) refl
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

private
  lemma : ∀ r p q → (↥ r ℤ.* ↧ p ℤ.+ ↥ p ℤ.* ↧ r) ℤ.* (↧ r ℤ.* ↧ q)
                    ≡ (↥ r ℤ.* ↧ r) ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ p ℤ.* ↧ q)
  lemma r p q = solve 5 (λ ↥r ↧r ↧p ↥p ↧q →
                          (↥r :* ↧p :+ ↥p :* ↧r) :* (↧r :* ↧q) :=
                          (↥r :* ↧r) :* (↧p :* ↧q) :+ (↧r :* ↧r) :* (↥p :* ↧q))
                      refl (↥ r) (↧ r) (↧ p) (↥ p) (↧ q)
    where open ℤ-solver

+-monoʳ-≤ : ∀ r → (r +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ r {p} {q} (*≤* x≤y) = *≤* $ begin
  ↥ (r + p) ℤ.* (↧ (r + q))                                ≡⟨ lemma r p q ⟩
  r₂ ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ p ℤ.* ↧ q)
    ≤⟨ ℤ.+-mono-≤ (ℤ.≤-reflexive $ cong (r₂ ℤ.*_) (ℤ.*-comm (↧ p) (↧ q)))
                  (ℤ.*-monoˡ-≤-non-neg (↧ₙ r ℕ.* ↧ₙ r) x≤y) ⟩
  r₂ ℤ.* (↧ q ℤ.* ↧ p) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ q ℤ.* ↧ p) ≡⟨ sym $ lemma r q p ⟩
  ↥ (r + q) ℤ.* (↧ (r + p))                                ∎
  where open ℤ.≤-Reasoning; r₂ = ↥ r ℤ.* ↧ r

+-monoˡ-≤ : ∀ r → (_+ r) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ r {p} {q} rewrite +-comm-≡ p r | +-comm-≡ q r = +-monoʳ-≤ r

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {p} {q} {u} {v} p≤q u≤v = ≤-trans (+-monoˡ-≤ u p≤q) (+-monoʳ-≤ q u≤v)

≤-steps : ∀ {p q r} → NonNegative r → p ≤ q → p ≤ r + q
≤-steps {p} {q} {r} r≥0 p≤q = subst (_≤ r + q) (+-identityˡ-≡ p) (+-mono-≤ (nonNegative⁻¹ r≥0) p≤q)

p≤p+q : ∀ {p q} → NonNegative q → p ≤ p + q
p≤p+q {p} {q} q≥0 = subst (_≤ p + q) (+-identityʳ-≡ p) (+-monoʳ-≤ p (nonNegative⁻¹ q≥0))

p≤q+p : ∀ {p} → NonNegative p → ∀ {q} → q ≤ p + q
p≤q+p {p} p≥0 {q} rewrite +-comm-≡ p q = p≤p+q p≥0

------------------------------------------------------------------------
-- Properties of _+_ and _<_

+-monoʳ-< : ∀ r → (r +_) Preserves _<_ ⟶ _<_
+-monoʳ-< r@(mkℚᵘ n dm) {p} {q} (*<* x<y) = *<* $ begin-strict
  ↥ (r + p) ℤ.* (↧ (r + q))                                   ≡⟨ lemma r p q ⟩
  r₂ ℤ.* (↧ p ℤ.* ↧ q) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ p ℤ.* ↧ q)
    <⟨ ℤ.+-mono-≤-< (ℤ.≤-reflexive $ cong (r₂ ℤ.*_) (ℤ.*-comm (↧ p) (↧ q)))
                    (ℤ.*-monoˡ-<-pos (dm ℕ.+ dm ℕ.* suc dm) x<y) ⟩
  r₂ ℤ.* (↧ q ℤ.* ↧ p) ℤ.+ (↧ r ℤ.* ↧ r) ℤ.* (↥ q ℤ.* ↧ p)    ≡⟨ sym $ lemma r q p ⟩
  ↥ (r + q) ℤ.* (↧ (r + p))                                   ∎
  where open ℤ.≤-Reasoning
        r₂ = n ℤ.* ↧ r

+-monoˡ-< : ∀ r → (_+ r) Preserves _<_ ⟶ _<_
+-monoˡ-< r {p} {q} rewrite +-comm-≡ p r | +-comm-≡ q r = +-monoʳ-< r

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {p} {q} {u} {v} p<q u<v = <-trans (+-monoˡ-< u p<q) (+-monoʳ-< q u<v)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {p} {q} {r} p≤q q<r = ≤-<-trans (+-monoˡ-≤ r p≤q) (+-monoʳ-< q q<r)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {p} {q} {r} p<q q≤r = <-≤-trans (+-monoˡ-< r p<q) (+-monoʳ-≤ q q≤r)

-----------------------------------------------------------------------
-- Properties of _-_

+-minus-telescope : ∀ p q r → (p - q) + (q - r) ≃ p - r
+-minus-telescope p q r = begin-equality
  (p - q) + (q - r)   ≈⟨ ≃-sym (+-assoc (p - q) q (- r)) ⟩
  (p - q) + q - r     ≈⟨ +-congˡ (- r) (+-assoc p (- q) q) ⟩
  (p + (- q + q)) - r ≈⟨ +-congˡ (- r) (+-congʳ p (+-inverseˡ q)) ⟩
  (p + 0ℚᵘ) - r       ≈⟨ +-congˡ (- r) (+-identityʳ p) ⟩
  p - r               ∎ where open ≤-Reasoning

p≃q⇒p-q≃0 : ∀ p q → p ≃ q → p - q ≃ 0ℚᵘ
p≃q⇒p-q≃0 p q p≃q = begin-equality
  p - q ≈⟨ +-congˡ (- q) p≃q ⟩
  q - q ≈⟨ +-inverseʳ q ⟩
  0ℚᵘ   ∎ where open ≤-Reasoning

p-q≃0⇒p≃q : ∀ p q → p - q ≃ 0ℚᵘ → p ≃ q
p-q≃0⇒p≃q p q p-q≃0 = begin-equality
  p             ≡˘⟨ +-identityʳ-≡ p ⟩
  p + 0ℚᵘ       ≈⟨ +-congʳ p (≃-sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡˘⟨ +-assoc-≡ p (- q) q ⟩
  (p - q) + q   ≈⟨ +-congˡ q p-q≃0 ⟩
  0ℚᵘ + q       ≡⟨ +-identityˡ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

neg-mono-≤-≥ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤-≥ {p} {q} (*≤* p≤q) = *≤* $ begin
  ℤ.- ↥ q ℤ.* ↧ p   ≡˘⟨ ℤ.neg-distribˡ-* (↥ q) (↧ p) ⟩
  ℤ.- (↥ q ℤ.* ↧ p) ≤⟨ ℤ.neg-mono-≤-≥ p≤q ⟩
  ℤ.- (↥ p ℤ.* ↧ q) ≡⟨ ℤ.neg-distribˡ-* (↥ p) (↧ q) ⟩
  ℤ.- ↥ p ℤ.* ↧ q   ∎ where open ℤ.≤-Reasoning

p≤q⇒p-q≤0 : ∀ {p q} → p ≤ q → p - q ≤ 0ℚᵘ
p≤q⇒p-q≤0 {p} {q} p≤q = begin
  p - q ≤⟨ +-monoˡ-≤ (- q) p≤q ⟩
  q - q ≈⟨ +-inverseʳ q ⟩
  0ℚᵘ   ∎ where open ≤-Reasoning

p-q≤0⇒p≤q : ∀ {p q} → p - q ≤ 0ℚᵘ → p ≤ q
p-q≤0⇒p≤q {p} {q} p-q≤0 = begin
  p             ≡˘⟨ +-identityʳ-≡ p ⟩
  p + 0ℚᵘ       ≈⟨ +-congʳ p (≃-sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡˘⟨ +-assoc-≡ p (- q) q ⟩
  (p - q) + q   ≤⟨ +-monoˡ-≤ q p-q≤0 ⟩
  0ℚᵘ + q       ≡⟨ +-identityˡ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

p≤q⇒0≤q-p : ∀ {p q} → p ≤ q → 0ℚᵘ ≤ q - p
p≤q⇒0≤q-p {p} {q} p≤q = begin
  0ℚᵘ   ≈⟨ ≃-sym (+-inverseʳ p) ⟩
  p - p ≤⟨ +-monoˡ-≤ (- p) p≤q ⟩
  q - p ∎ where open ≤-Reasoning

0≤q-p⇒p≤q : ∀ {p q} → 0ℚᵘ ≤ q - p → p ≤ q
0≤q-p⇒p≤q {p} {q} 0≤p-q = begin
  p             ≡˘⟨ +-identityˡ-≡ p ⟩
  0ℚᵘ + p       ≤⟨ +-monoˡ-≤ p 0≤p-q ⟩
  q - p + p     ≡⟨ +-assoc-≡ q (- p) p ⟩
  q + (- p + p) ≈⟨ +-congʳ q (+-inverseˡ p) ⟩
  q + 0ℚᵘ       ≡⟨ +-identityʳ-≡ q ⟩
  q             ∎ where open ≤-Reasoning

------------------------------------------------------------------------
-- Algebraic structures

+-isMagma : IsMagma _≃_ _+_
+-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong        = +-cong
  }

+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-0-isMonoid : IsMonoid _≃_ _+_ 0ℚᵘ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+_ 0ℚᵘ
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

+-0-isGroup : IsGroup _≃_ _+_ 0ℚᵘ (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverse
  ; ⁻¹-cong  = -‿cong
  }

+-0-isAbelianGroup : IsAbelianGroup _≃_ _+_ 0ℚᵘ (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

------------------------------------------------------------------------
-- Algebraic bundles

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Raw bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  }

*-rawMonoid : RawMonoid 0ℓ 0ℓ
*-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  ; ε   = 1ℚᵘ
  }

------------------------------------------------------------------------
-- Algebraic properties

*-cong : Congruent₂ _≃_ _*_
*-cong {x} {y} {u} {v} (*≡* ↥x↧y≡↥y↧x) (*≡* ↥u↧v≡↥v↧u) = *≡* (begin
  (↥ x ℤ.* ↥ u) ℤ.* (↧ y ℤ.* ↧ v) ≡⟨ solve 4 (λ ↥x ↥u ↧y ↧v →
                                       (↥x :* ↥u) :* (↧y :* ↧v) :=
                                       (↥u :* ↧v) :* (↥x :* ↧y))
                                       refl (↥ x) (↥ u) (↧ y) (↧ v) ⟩
  (↥ u ℤ.* ↧ v) ℤ.* (↥ x ℤ.* ↧ y) ≡⟨ cong₂ ℤ._*_ ↥u↧v≡↥v↧u ↥x↧y≡↥y↧x ⟩
  (↥ v ℤ.* ↧ u) ℤ.* (↥ y ℤ.* ↧ x) ≡⟨ solve 4 (λ ↥v ↧u ↥y ↧x →
                                       (↥v :* ↧u) :* (↥y :* ↧x) :=
                                       (↥y :* ↥v) :* (↧x :* ↧u))
                                       refl (↥ v) (↧ u) (↥ y) (↧ x) ⟩
  (↥ y ℤ.* ↥ v) ℤ.* (↧ x ℤ.* ↧ u) ∎)
  where open ≡-Reasoning; open ℤ-solver

-- Associativity

*-assoc-↥ : Associative (_≡_ on ↥_) _*_
*-assoc-↥ p q r = ℤ.*-assoc (↥ p) (↥ q) (↥ r)

*-assoc-↧ : Associative (_≡_ on ↧ₙ_) _*_
*-assoc-↧ p q r = ℕ.*-assoc (↧ₙ p) (↧ₙ q) (↧ₙ r)

*-assoc-≡ : Associative _≡_ _*_
*-assoc-≡ p q r = ↥↧≡⇒≡ (*-assoc-↥ p q r) (*-assoc-↧ p q r)

*-assoc : Associative _≃_ _*_
*-assoc p q r = ≃-reflexive (*-assoc-≡ p q r)

-- Commutativity

*-comm-↥ : Commutative (_≡_ on ↥_) _*_
*-comm-↥ p q = ℤ.*-comm (↥ p) (↥ q)

*-comm-↧ : Commutative (_≡_ on ↧ₙ_) _*_
*-comm-↧ p q = ℕ.*-comm (↧ₙ p) (↧ₙ q)

*-comm-≡ : Commutative _≡_ _*_
*-comm-≡ p q = ↥↧≡⇒≡ (*-comm-↥ p q) (*-comm-↧ p q)

*-comm : Commutative _≃_ _*_
*-comm p q = ≃-reflexive (*-comm-≡ p q)

-- Identities

*-identityˡ-≡ : LeftIdentity _≡_ 1ℚᵘ _*_
*-identityˡ-≡ p = ↥↧≡⇒≡ (ℤ.*-identityˡ (↥ p)) (ℕ.+-identityʳ (↧ₙ p))

*-identityʳ-≡ : RightIdentity _≡_ 1ℚᵘ _*_
*-identityʳ-≡ = comm+idˡ⇒idʳ *-comm-≡ {e = 1ℚᵘ} *-identityˡ-≡

*-identity-≡ : Identity _≡_ 1ℚᵘ _*_
*-identity-≡ = *-identityˡ-≡ , *-identityʳ-≡

*-identityˡ : LeftIdentity _≃_ 1ℚᵘ _*_
*-identityˡ p = ≃-reflexive (*-identityˡ-≡ p)

*-identityʳ : RightIdentity _≃_ 1ℚᵘ _*_
*-identityʳ p = ≃-reflexive (*-identityʳ-≡ p)

*-identity : Identity _≃_ 1ℚᵘ _*_
*-identity = *-identityˡ , *-identityʳ

*-inverseˡ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → 1/_ p {p≢0} * p ≃ 1ℚᵘ
*-inverseˡ p@(mkℚᵘ -[1+ n ] d) = *-inverseˡ (mkℚᵘ +[1+ n ] d)
*-inverseˡ p@(mkℚᵘ +[1+ n ] d) = *≡* $ cong +[1+_] $ begin
  (n ℕ.+ d ℕ.* suc n) ℕ.* 1 ≡⟨ ℕ.*-identityʳ _ ⟩
  (n ℕ.+ d ℕ.* suc n)       ≡⟨ cong (n ℕ.+_) (ℕ.*-suc d n) ⟩
  (n ℕ.+ (d ℕ.+ d ℕ.* n))   ≡⟨ solve 2 (λ n d → n :+ (d :+ d :* n) := d :+ (n :+ n :* d)) refl n d ⟩
  (d ℕ.+ (n ℕ.+ n ℕ.* d))   ≡⟨ cong (d ℕ.+_) (sym (ℕ.*-suc n d)) ⟩
  d ℕ.+ n ℕ.* suc d         ≡˘⟨ ℕ.+-identityʳ _ ⟩
  d ℕ.+ n ℕ.* suc d ℕ.+ 0   ∎
  where open ≡-Reasoning; open ℕ-solver

*-inverseʳ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → p * 1/_ p {p≢0} ≃ 1ℚᵘ
*-inverseʳ p {p≢0} = ≃-trans (*-comm p (1/ p)) (*-inverseˡ p {p≢0})

*-zeroˡ : LeftZero _≃_ 0ℚᵘ _*_
*-zeroˡ p = *≡* refl

*-zeroʳ : RightZero _≃_ 0ℚᵘ _*_
*-zeroʳ = FC.comm+zeˡ⇒zeʳ ≃-setoid *-comm *-zeroˡ

*-zero : Zero _≃_ 0ℚᵘ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ p q r =
  let ↥p = ↥ p; ↧p = ↧ p
      ↥q = ↥ q; ↧q = ↧ q
      ↥r = ↥ r; ↧r = ↧ r
      eq : (↥p ℤ.* (↥q ℤ.* ↧r ℤ.+ ↥r ℤ.* ↧q)) ℤ.* (↧p ℤ.* ↧q ℤ.* (↧p ℤ.* ↧r)) ≡
           (↥p ℤ.* ↥q ℤ.* (↧p ℤ.* ↧r) ℤ.+ ↥p ℤ.* ↥r ℤ.* (↧p ℤ.* ↧q)) ℤ.* (↧p ℤ.* (↧q ℤ.* ↧r))
      eq = solve 6 (λ ↥p ↧p ↥q d e f →
           (↥p :* (↥q :* f :+ e :* d)) :* (↧p :* d :* (↧p :* f)) :=
           (↥p :* ↥q :* (↧p :* f) :+ ↥p :* e :* (↧p :* d)) :* (↧p :* (d :* f)))
           refl ↥p ↧p ↥q ↧q ↥r ↧r
  in *≡* eq where open ℤ-solver

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ = FC.comm+distrˡ⇒distrʳ ≃-setoid +-cong *-comm *-distribˡ-+

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

------------------------------------------------------------------------
-- Properties of _*_ and -_

neg-distribˡ-* : ∀ p q → - (p * q) ≃ - p * q
neg-distribˡ-* p q = *≡* $ cong (ℤ._* (↧ p ℤ.* ↧ q))
                         $ ℤ.neg-distribˡ-* (↥ p) (↥ q)

neg-distribʳ-* : ∀ p q → - (p * q) ≃ p * - q
neg-distribʳ-* p q = *≡* $ cong (ℤ._* (↧ p ℤ.* ↧ q))
                         $ ℤ.neg-distribʳ-* (↥ p) (↥ q)
------------------------------------------------------------------------
-- Properties of _*_ and _≤_

private
  reorder₁ : ∀ a b c d → a ℤ.* b ℤ.* (c ℤ.* d) ≡ a ℤ.* c ℤ.* b ℤ.* d
  reorder₁ = solve 4 (λ a b c d → a :* b :* (c :* d) := a :* c :* b :* d) refl
    where open ℤ-solver

  reorder₂ : ∀ a b c d → a ℤ.* b ℤ.* (c ℤ.* d) ≡ a ℤ.* c ℤ.* (b ℤ.* d)
  reorder₂ = solve 4 (λ a b c d → a :* b :* (c :* d) := a :* c :* (b :* d)) refl
    where open ℤ-solver

*-cancelʳ-≤-pos : ∀ {r} → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
*-cancelʳ-≤-pos {mkℚᵘ +[1+ n ] dm} _ {p} {q} (*≤* x≤y)
  = let o = dm ℕ.+ n ℕ.* suc dm ; l₁ = ↥ p ℤ.* ↧ q ; l₂ = ↥ q ℤ.* ↧ p
  in *≤* $ ℤ.*-cancelʳ-≤-pos l₁ l₂ o $ begin
  l₁ ℤ.* (+[1+ n ] ℤ.* +[1+ dm ])          ≡⟨ reorder₂ (↥ p) _ _ (ℤ.+ (suc dm)) ⟩
  ↥ p ℤ.* +[1+ n ] ℤ.* (↧ q ℤ.* +[1+ dm ]) ≤⟨ x≤y ⟩
  ↥ q ℤ.* +[1+ n ] ℤ.* (↧ p ℤ.* +[1+ dm ]) ≡⟨ reorder₂ (↥ q) _ _ (ℤ.+ (suc dm)) ⟩
  l₂ ℤ.* (+[1+ n ] ℤ.* +[1+ dm ])          ∎ where open ℤ.≤-Reasoning

*-cancelˡ-≤-pos : ∀ {r} → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
*-cancelˡ-≤-pos {r} r>0 {p} {q}
  rewrite *-comm-≡ r p
        | *-comm-≡ r q = *-cancelʳ-≤-pos r>0

*-monoˡ-≤-nonNeg : ∀ {r} → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-nonNeg r@{mkℚᵘ (ℤ.+ n) _} _ {p} {q} (*≤* x<y) = *≤* $ begin
  ↥ p ℤ.* ↥ r ℤ.* (↧ q   ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ p) _ _ _ ⟩
  l₁          ℤ.* (ℤ.+ n ℤ.* ↧ r)  ≡⟨ cong (l₁ ℤ.*_) (ℤ.pos-distrib-* n _) ⟩
  l₁          ℤ.* ℤ.+ (n ℕ.* ↧ₙ r) ≤⟨ ℤ.*-monoʳ-≤-non-neg (n ℕ.* _) x<y ⟩
  l₂          ℤ.* ℤ.+ (n ℕ.* ↧ₙ r) ≡⟨ cong (l₂ ℤ.*_) (sym (ℤ.pos-distrib-* n _)) ⟩
  l₂          ℤ.* (ℤ.+ n ℤ.* ↧ r)  ≡⟨ reorder₂ (↥ q) _ _ _ ⟩
  ↥ q ℤ.* ↥ r ℤ.* (↧ p   ℤ.* ↧ r)  ∎
  where open ℤ.≤-Reasoning
        l₁ = ↥ p ℤ.* ↧ q ; l₂ = ↥ q ℤ.* ↧ p

*-monoʳ-≤-nonNeg : ∀ {r} → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-nonNeg {r} r≥0 {p} {q}
  rewrite *-comm-≡ r p
        | *-comm-≡ r q = *-monoˡ-≤-nonNeg r≥0

*-monoʳ-≤-pos : ∀ {r} → Positive r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos {r} = (*-monoʳ-≤-nonNeg {r}) ∘ (positive⇒nonNegative {r})

*-monoˡ-≤-pos : ∀ {r} → Positive r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos {r} = *-monoˡ-≤-nonNeg ∘ (positive⇒nonNegative {r})

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ {r} (r>0 : Positive r) → (_* r) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos s@{mkℚᵘ +[1+ n ] d} _ {p} {q} (*<* x<y) = *<* $ begin-strict
  ↥ p ℤ.*  ↥ s ℤ.* (↧ q  ℤ.* ↧ s) ≡⟨ reorder₁ (↥ p) _ _ _ ⟩
  ↥ p ℤ.*  ↧ q ℤ.*  ↥ s  ℤ.* ↧ s  <⟨ ℤ.*-monoʳ-<-pos d (ℤ.*-monoʳ-<-pos n x<y) ⟩
  ↥ q ℤ.*  ↧ p ℤ.*  ↥ s  ℤ.* ↧ s  ≡˘⟨ reorder₁ (↥ q) _ _ _ ⟩
  ↥ q ℤ.*  ↥ s ℤ.* (↧ p  ℤ.* ↧ s) ∎ where open ℤ.≤-Reasoning

*-monoʳ-<-pos : ∀ {r} (r>0 : Positive r) → (r *_) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos {r} r>0 {p} {q}
  rewrite *-comm-≡ r p
        | *-comm-≡ r q = *-monoˡ-<-pos r>0

*-cancelˡ-<-nonNeg : ∀ {r} (r≥0 : NonNegative r) {p q} → r * p < r * q → p < q
*-cancelˡ-<-nonNeg {mkℚᵘ (ℤ.+ n) dm} _ {p} {q} (*<* x<y) = *<* $
  ℤ.*-cancelˡ-<-non-neg s $ begin-strict
  ℤ.+ s         ℤ.* r₁          ≡⟨ cong (ℤ._* r₁) (sym (ℤ.pos-distrib-* n (suc dm))) ⟩
  ℤ.+ n ℤ.* d   ℤ.* r₁          ≡⟨ reorder₂ (ℤ.+ n) _ _ _ ⟩
  ℤ.+ n ℤ.* ↥ p ℤ.* (d ℤ.* ↧ q) <⟨ x<y ⟩
  ℤ.+ n ℤ.* ↥ q ℤ.* (d ℤ.* ↧ p) ≡⟨ reorder₂ (ℤ.+ n) _ _ _ ⟩
  ℤ.+ n ℤ.* d   ℤ.* r₂          ≡⟨ cong (ℤ._* r₂) ( ℤ.pos-distrib-* n (suc dm)) ⟩
  ℤ.+ s ℤ.* r₂                  ∎
  where open ℤ.≤-Reasoning
        d+ = suc dm ; s = n ℕ.* d+ ; d = ℤ.+ d+ ; r₁ = ↥ p ℤ.* ↧ q ; r₂ = ↥ q ℤ.* ↧ p

*-cancelʳ-<-nonNeg : ∀ {r} (r≥0 : NonNegative r) {p q} → p * r < q * r → p < q
*-cancelʳ-<-nonNeg {r} r≥0 {p} {q}
  rewrite *-comm-≡ p r
        | *-comm-≡ q r = *-cancelˡ-<-nonNeg {r} r≥0

------------------------------------------------------------------------
-- Algebraic structures

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong        = *-cong
  }

*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _≃_ _*_ 1ℚᵘ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ 1ℚᵘ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isRing : IsRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-isCommutativeRing : IsCommutativeRing _≃_ _+_ _*_ -_ 0ℚᵘ 1ℚᵘ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

------------------------------------------------------------------------
-- Algebraic bundles

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

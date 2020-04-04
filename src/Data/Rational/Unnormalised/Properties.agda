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
open import Data.Nat.Base using (suc; pred)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base as ℤ using (ℤ; +0; +[1+_]; 0ℤ; 1ℤ)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤ-solver)
import Data.Integer.Properties as ℤ
import Data.Integer.Properties
open import Data.Rational.Unnormalised
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

↥-neg-≡ : ∀ p → ↥ (- p) ≡ ℤ.- (↥ p)
↥-neg-≡ p = refl
-- ↥-neg-≡ (mkℚᵘ ℤ.-[1+ _ ] _) = refl
-- ↥-neg-≡ (mkℚᵘ ℤ.+0       _) = refl
-- ↥-neg-≡ (mkℚᵘ ℤ.+[1+ _ ] _) = refl

↧-neg-≡ : ∀ p → ↧ (- p) ≡ (↧ p)
↧-neg-≡ (mkℚᵘ ℤ.-[1+ _ ] _) = refl
↧-neg-≡ (mkℚᵘ ℤ.+0       _) = refl
↧-neg-≡ (mkℚᵘ ℤ.+[1+ _ ] _) = refl


------------------------------------------------------------------------
-- Properties of -_
------------------------------------------------------------------------

neg-mono-<-> : -_ Preserves  _<_ ⟶ _>_
neg-mono-<-> {m} {n} (*<* m<n) = *<* $ begin-strict
  ℤ.-  ↥ n ℤ.* ↧ m    ≡⟨ sym (ℤ.neg-distribˡ-* (↥ n) (↧ m)) ⟩
  ℤ.- (↥ n ℤ.* ↧ m)   <⟨ ℤ.neg-mono-<-> m<n ⟩
  ℤ.- (↥ m ℤ.* ↧ n)   ≡⟨ ℤ.neg-distribˡ-* (↥ m) (↧ n) ⟩
  ↥ (- m) ℤ.* ↧ (- n) ∎
  where open ℤ.≤-Reasoning

neg-involutive-≡ : Involutive _≡_ (-_)
neg-involutive-≡ (mkℚᵘ n d) = cong (λ n → mkℚᵘ n d) (ℤ.neg-involutive n)

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {p} {q} (*≡* p≡q) = *≡* (begin
  ↥(- p) ℤ.* ↧ q             ≡˘⟨ ℤ.*-identityˡ (ℤ.-(↥ p) ℤ.* ↧ q) ⟩
  1ℤ ℤ.* (↥(- p) ℤ.* ↧ q)    ≡⟨ sym (ℤ.*-assoc 1ℤ (↥(- p)) (↧ q)) ⟩
  (1ℤ ℤ.* ℤ.-(↥ p)) ℤ.* ↧ q  ≡˘⟨ cong (ℤ._* ↧ q) (ℤ.neg-distribʳ-* 1ℤ (↥ p)) ⟩
  ℤ.-(1ℤ ℤ.* ↥ p) ℤ.* ↧ q    ≡⟨ cong (ℤ._* ↧ q) (ℤ.neg-distribˡ-* 1ℤ (↥ p)) ⟩
  ((ℤ.- 1ℤ) ℤ.* ↥ p) ℤ.* ↧ q ≡⟨ ℤ.*-assoc (ℤ.- 1ℤ) (↥ p) (↧ q) ⟩
  ℤ.- 1ℤ ℤ.* (↥ p ℤ.* ↧ q)   ≡⟨ cong (λ r → ℤ.- 1ℤ ℤ.* r) p≡q ⟩
  ℤ.- 1ℤ ℤ.* (↥ q ℤ.* ↧ p)   ≡⟨ sym (ℤ.*-assoc (ℤ.- 1ℤ) (↥ q) (↧ p)) ⟩
  (ℤ.- 1ℤ ℤ.* ↥ q) ℤ.* ↧ p   ≡˘⟨ cong (ℤ._* ↧ p) (ℤ.neg-distribˡ-* 1ℤ (↥ q)) ⟩
  ℤ.-(1ℤ ℤ.* ↥ q) ℤ.* ↧ p    ≡⟨ cong (ℤ._* ↧ p) (ℤ.neg-distribʳ-* 1ℤ (↥ q)) ⟩
  (1ℤ ℤ.* ↥(- q)) ℤ.* ↧ p    ≡⟨ ℤ.*-assoc 1ℤ (ℤ.-(↥ q)) (↧ p) ⟩
  1ℤ ℤ.* (↥(- q) ℤ.* ↧ p)    ≡⟨ ℤ.*-identityˡ (↥(- q) ℤ.* ↧ p) ⟩
  ↥(- q) ℤ.* ↧ p ∎) where open ≡-Reasoning


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
  (n₃  ℤ.* d₁) ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning

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
-- Properties of _<_
------------------------------------------------------------------------

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {p} {q} {r} (*≤* p≤q) (*<* q<r)
  = let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r in *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  (n₁ ℤ.*  d₃) ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
   n₁ ℤ.* (d₃  ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
   n₁ ℤ.* (d₂  ℤ.* d₃) ≡⟨ sym (ℤ.*-assoc n₁ d₂ d₃) ⟩
  (n₁ ℤ.*  d₂) ℤ.* d₃  ≤⟨ ℤ.*-monoʳ-≤-pos (pred (↧ₙ r)) p≤q ⟩
  (n₂ ℤ.*  d₁) ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  (d₁ ℤ.*  n₂) ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
   d₁ ℤ.* (n₂  ℤ.* d₃) <⟨ ℤ.*-monoˡ-<-pos (pred (↧ₙ p)) q<r ⟩
   d₁ ℤ.* (n₃  ℤ.* d₂) ≡⟨ sym (ℤ.*-assoc d₁ n₃ d₂) ⟩
  (d₁ ℤ.*  n₃) ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  (n₃ ℤ.*  d₁) ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r)
  = let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r in *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  (n₁ ℤ.*  d₃) ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
   n₁ ℤ.* (d₃  ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
   n₁ ℤ.* (d₂  ℤ.* d₃) ≡⟨ sym (ℤ.*-assoc n₁ d₂ d₃) ⟩
  (n₁ ℤ.*  d₂) ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (pred (↧ₙ r)) p<q ⟩
  (n₂ ℤ.*  d₁) ℤ.* d₃  ≡⟨ cong (ℤ._* d₃) (ℤ.*-comm n₂ d₁) ⟩
  (d₁ ℤ.*  n₂) ℤ.* d₃  ≡⟨ ℤ.*-assoc d₁ n₂ d₃ ⟩
   d₁ ℤ.* (n₂  ℤ.* d₃) ≤⟨ ℤ.*-monoˡ-≤-pos (pred (↧ₙ p)) q≤r ⟩
   d₁ ℤ.* (n₃  ℤ.* d₂) ≡⟨ sym (ℤ.*-assoc d₁ n₃ d₂) ⟩
  (d₁ ℤ.*  n₃) ℤ.* d₂  ≡⟨ cong (ℤ._* d₂) (ℤ.*-comm d₁ n₃) ⟩
  (n₃ ℤ.*  d₁) ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning

-- Relational properties

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

<-trans : Transitive _<_
<-trans = ≤-<-trans ∘ <⇒≤

<-respʳ-≈ : _<_ Respectsʳ _≃_
<-respʳ-≈ {p} {q} {r} (*≡* q≡r) (*<* p<q)
  = let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; d₁ = ↧ p; d₂ = ↧ q; d₃ = ↧ r in *<* $
  ℤ.*-cancelʳ-<-non-neg _ $ begin-strict
  (n₁ ℤ.*  d₃) ℤ.* d₂  ≡⟨ ℤ.*-assoc n₁ d₃ d₂ ⟩
   n₁ ℤ.* (d₃  ℤ.* d₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm d₃ d₂) ⟩
   n₁ ℤ.* (d₂  ℤ.* d₃) ≡⟨ sym (ℤ.*-assoc n₁ d₂ d₃) ⟩
  (n₁ ℤ.*  d₂) ℤ.* d₃  <⟨ ℤ.*-monoʳ-<-pos (pred (↧ₙ r)) p<q ⟩
  (n₂ ℤ.*  d₁) ℤ.* d₃  ≡⟨ ℤ.*-assoc n₂ d₁ d₃ ⟩
   n₂ ℤ.* (d₁  ℤ.* d₃) ≡⟨ cong (n₂ ℤ.*_) (ℤ.*-comm d₁ d₃) ⟩
   n₂ ℤ.* (d₃  ℤ.* d₁) ≡⟨ sym (ℤ.*-assoc n₂ d₃ d₁) ⟩
  (n₂ ℤ.*  d₃) ℤ.* d₁  ≡⟨ cong (ℤ._* d₁) q≡r ⟩
  (n₃ ℤ.*  d₂) ℤ.* d₁  ≡⟨ ℤ.*-assoc n₃ d₂ d₁ ⟩
   n₃ ℤ.* (d₂  ℤ.* d₁) ≡⟨ cong (n₃ ℤ.*_) (ℤ.*-comm d₂ d₁) ⟩
   n₃ ℤ.* (d₁  ℤ.* d₂) ≡⟨ sym (ℤ.*-assoc n₃ d₁ d₂) ⟩
  (n₃ ℤ.*  d₁) ℤ.* d₂  ∎
  where open ℤ.≤-Reasoning

<-respˡ-≈ : _<_ Respectsˡ _≃_
<-respˡ-≈ q≃r q<p
  = subst (_< _) (neg-involutive-≡ _)
  $ subst (_ <_) (neg-involutive-≡ _)
  $ neg-mono-<-> (<-respʳ-≈ (-‿cong q≃r) (neg-mono-<-> q<p))

<-resp-≈ : _<_ Respects₂ _≃_
<-resp-≈ = <-respʳ-≈ , <-respˡ-≈


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

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≈
    <⇒≤
    <-≤-trans
    ≤-<-trans

------------------------------------------------------------------------
-- Bundles

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

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
  ↥ p                       ∎
  where open ≡-Reasoning

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
  0ℤ ∎ where open ≡-Reasoning

+-inverseʳ : RightInverse _≃_ 0ℚᵘ -_ _+_
+-inverseʳ p = *≡* let n = ↥ p; d = ↧ p in
  (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ℤ.* 1ℤ ≡⟨ ℤ.*-identityʳ (n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d) ⟩
  n ℤ.* d ℤ.+ (ℤ.- n) ℤ.* d          ≡˘⟨ cong (λ n+d → n ℤ.* d ℤ.+ n+d) (ℤ.neg-distribˡ-* n d) ⟩
  n ℤ.* d ℤ.+ ℤ.- (n ℤ.* d)          ≡⟨ ℤ.+-inverseʳ (n ℤ.* d) ⟩
  0ℤ ∎ where open ≡-Reasoning

+-inverse : Inverse _≃_ 0ℚᵘ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ


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

*-monoʳ-<-pos : ∀ n d → (_* mkℚᵘ (ℤ.+[1+ n ]) d) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos n d {x} {y} (*<* x<y)
  = let s = mkℚᵘ (ℤ.+ suc n) d in *<* $ begin-strict
  (↥ x ℤ.*  ↥ s) ℤ.* (↧ y  ℤ.* ↧ s) ≡⟨ sym (ℤ.*-assoc (↥ x ℤ.* ↥ s) _ _) ⟩
  (↥ x ℤ.*  ↥ s) ℤ.*  ↧ y  ℤ.* ↧ s  ≡⟨ cong (ℤ._* ↧ s) (ℤ.*-assoc (↥ x) _ _) ⟩
   ↥ x ℤ.* (↥ s  ℤ.*  ↧ y) ℤ.* ↧ s  ≡⟨ cong (ℤ._* ↧ s) (cong (↥ x ℤ.*_) (ℤ.*-comm (↥ s) (↧ y))) ⟩
   ↥ x ℤ.* (↧ y  ℤ.*  ↥ s) ℤ.* ↧ s  ≡⟨ sym ( cong (ℤ._* ↧ s) (ℤ.*-assoc (↥ x) _ _)) ⟩
  (↥ x ℤ.*  ↧ y) ℤ.*  ↥ s  ℤ.* ↧ s  <⟨ ℤ.*-monoʳ-<-pos d (ℤ.*-monoʳ-<-pos n x<y) ⟩
  (↥ y ℤ.*  ↧ x) ℤ.*  ↥ s  ℤ.* ↧ s  ≡⟨ cong (ℤ._* ↧ s) (ℤ.*-assoc (↥ y) _ _) ⟩
   ↥ y ℤ.* (↧ x  ℤ.*  ↥ s) ℤ.* ↧ s  ≡⟨ cong (ℤ._* ↧ s) (cong (↥ y ℤ.*_) (ℤ.*-comm (↧ x) (↥ s))) ⟩
   ↥ y ℤ.* (↥ s  ℤ.*  ↧ x) ℤ.* ↧ s  ≡⟨ sym (cong (ℤ._* ↧ s) (ℤ.*-assoc (↥ y) _ _)) ⟩
   ↥ y ℤ.*  ↥ s  ℤ.*  ↧ x  ℤ.* ↧ s  ≡⟨ ℤ.*-assoc (↥ y ℤ.* ↥ s) _ _ ⟩
  (↥ y ℤ.*  ↥ s) ℤ.* ↧ (x    *   s) ∎
  where open ℤ.≤-Reasoning

*-monoˡ-<-pos : ∀ n d → (mkℚᵘ (ℤ.+[1+ n ]) d *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos n d {x} {y} x<y
  rewrite *-comm-≡ (mkℚᵘ (ℤ.+[1+ n ]) d) x
        | *-comm-≡ (mkℚᵘ (ℤ.+[1+ n ]) d) y
        = *-monoʳ-<-pos n d x<y

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



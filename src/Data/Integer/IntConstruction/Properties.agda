{-# OPTIONS --safe --cubical-compatible #-}

module Data.Integer.IntConstruction.Properties where

import Algebra.Properties.CommutativeSemigroup as CommSemigroupProps
open import Data.Integer.IntConstruction
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Function.Base
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Algebra.Definitions _≃_

private
  trans-helper
    : ∀ {r} (R : Rel ℕ r)
      → ∀ a b c d e f
      → R (a ℕ.+ d ℕ.+ (c ℕ.+ f)) (c ℕ.+ b ℕ.+ (e ℕ.+ d))
     → R ((a ℕ.+ f) ℕ.+ (d ℕ.+ c)) ((e ℕ.+ b) ℕ.+ (d ℕ.+ c))
  trans-helper R a b c d e f mono = subst₂ R preamble postamble mono
    where
      open ≡-Reasoning
      open CommSemigroupProps ℕ.+-commutativeSemigroup
      preamble : (a ℕ.+ d) ℕ.+ (c ℕ.+ f) ≡ (a ℕ.+ f) ℕ.+ (d ℕ.+ c)
      preamble = begin
        (a ℕ.+ d) ℕ.+ (c ℕ.+ f) ≡⟨ cong (a ℕ.+ d ℕ.+_) (ℕ.+-comm c f) ⟩
        (a ℕ.+ d) ℕ.+ (f ℕ.+ c) ≡⟨ medial a d f c ⟩
        (a ℕ.+ f) ℕ.+ (d ℕ.+ c) ∎
      postamble : (c ℕ.+ b) ℕ.+ (e ℕ.+ d) ≡ (e ℕ.+ b) ℕ.+ (d ℕ.+ c)
      postamble = begin
        (c ℕ.+ b) ℕ.+ (e ℕ.+ d) ≡⟨ ℕ.+-comm (c ℕ.+ b) (e ℕ.+ d) ⟩
        (e ℕ.+ d) ℕ.+ (c ℕ.+ b) ≡⟨ cong (e ℕ.+ d ℕ.+_) (ℕ.+-comm c b) ⟩
        (e ℕ.+ d) ℕ.+ (b ℕ.+ c) ≡⟨ medial e d b c ⟩
        (e ℕ.+ b) ℕ.+ (d ℕ.+ c) ∎

------------------------------------------------------------------------
-- Properties of _≃_

≃-refl : Reflexive _≃_
≃-refl = refl

≃-sym : Symmetric _≃_
≃-sym = sym

≃-trans : Transitive _≃_
≃-trans {a ⊖ b} {c ⊖ d} {e ⊖ f} i≃j j≃k = ℕ.+-cancelʳ-≡ (d ℕ.+ c) (a ℕ.+ f) (e ℕ.+ b) $ trans-helper _≡_ a b c d e f (cong₂ ℕ._+_ i≃j j≃k)

_≃?_ : Decidable _≃_
(a ⊖ b) ≃? (c ⊖ d) = a ℕ.+ d ℕ.≟ c ℕ.+ b

------------------------------------------------------------------------
-- Properties of _≤_

≤-refl : Reflexive _≤_
≤-refl = ℕ.≤-refl

≤-trans : Transitive _≤_
≤-trans {a ⊖ b} {c ⊖ d} {e ⊖ f} i≤j j≤k = ℕ.+-cancelʳ-≤ (d ℕ.+ c) (a ℕ.+ f) (e ℕ.+ b) $ trans-helper ℕ._≤_ a b c d e f (ℕ.+-mono-≤ i≤j j≤k)

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym i≤j j≤i = ℕ.≤-antisym i≤j j≤i

≤-total : Total _≤_
≤-total (a ⊖ b) (c ⊖ d) = ℕ.≤-total (a ℕ.+ d) (c ℕ.+ b)

_≤?_ : Decidable _≤_
(a ⊖ b) ≤? (c ⊖ d) = a ℕ.+ d ℕ.≤? c ℕ.+ b

------------------------------------------------------------------------
-- Properties of _<_

<-irrefl : Irreflexive _≃_ _<_
<-irrefl = ℕ.<-irrefl

<-trans : Transitive _<_
<-trans {a ⊖ b} {c ⊖ d} {e ⊖ f} i<j j<k = ℕ.+-cancelʳ-< (d ℕ.+ c) (a ℕ.+ f) (e ℕ.+ b) $ trans-helper ℕ._<_ a b c d e f (ℕ.+-mono-< i<j j<k)

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ {a ⊖ b} {c ⊖ d} {e ⊖ f} j≃k i>j = ℕ.+-cancelʳ-< (d ℕ.+ c) (e ℕ.+ b) (a ℕ.+ f) $ trans-helper ℕ._>_ a b c d e f (ℕ.+-mono-<-≤ i>j (ℕ.≤-reflexive (sym j≃k)))

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ {a ⊖ b} {c ⊖ d} {e ⊖ f} j≃k i<j = ℕ.+-cancelʳ-< (d ℕ.+ c) (a ℕ.+ f) (e ℕ.+ b) $ trans-helper ℕ._<_ a b c d e f (ℕ.+-mono-<-≤ i<j (ℕ.≤-reflexive j≃k))

_<?_ : Decidable _<_
(a ⊖ b) <? (c ⊖ d) = a ℕ.+ d ℕ.<? c ℕ.+ b

<-cmp : Trichotomous _≃_ _<_
<-cmp (a ⊖ b) (c ⊖ d) = ℕ.<-cmp (a ℕ.+ d) (c ℕ.+ b)

------------------------------------------------------------------------
-- Algebraic properties of _+_

+-cong : Congruent₂ _+_
+-cong {a ⊖ b} {c ⊖ d} {e ⊖ f} {g ⊖ h} a+d≡c+b e+h≡g+f = begin
  (a ℕ.+ e) ℕ.+ (d ℕ.+ h) ≡⟨ medial a e d h ⟩
  (a ℕ.+ d) ℕ.+ (e ℕ.+ h) ≡⟨ cong₂ ℕ._+_ a+d≡c+b e+h≡g+f ⟩
  (c ℕ.+ b) ℕ.+ (g ℕ.+ f) ≡⟨ medial c b g f ⟩
  (c ℕ.+ g) ℕ.+ (b ℕ.+ f) ∎
  where
    open ≡-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup

+-assoc : Associative _+_
+-assoc (a ⊖ b) (c ⊖ d) (e ⊖ f) = cong₂ ℕ._+_ (ℕ.+-assoc a c e) (sym (ℕ.+-assoc b d f))

+-identityˡ : LeftIdentity 0ℤ _+_
+-identityˡ (a ⊖ b) = refl

+-identityʳ : RightIdentity 0ℤ _+_
+-identityʳ (a ⊖ b) = cong₂ ℕ._+_ (ℕ.+-identityʳ a) (sym (ℕ.+-identityʳ b))

+-comm : Commutative _+_
+-comm (a ⊖ b) (c ⊖ d) = cong₂ ℕ._+_ (ℕ.+-comm a c) (ℕ.+-comm d b)

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

+-mono-≤ : Monotonic₂ _≤_ _≤_ _≤_ _+_
+-mono-≤ {a ⊖ b} {c ⊖ d} {e ⊖ f} {g ⊖ h} a+d≤c+b e+h≤g+f = begin
  (a ℕ.+ e) ℕ.+ (d ℕ.+ h) ≡⟨ medial a e d h ⟩
  (a ℕ.+ d) ℕ.+ (e ℕ.+ h) ≤⟨ ℕ.+-mono-≤ a+d≤c+b e+h≤g+f ⟩
  (c ℕ.+ b) ℕ.+ (g ℕ.+ f) ≡⟨ medial c b g f ⟩
  (c ℕ.+ g) ℕ.+ (b ℕ.+ f) ∎
  where
    open ℕ.≤-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup

------------------------------------------------------------------------
-- Algebraic properties of -_

-‿cong : Congruent₁ -_
-‿cong {a ⊖ b} {c ⊖ d} a+d≡c+b = begin
  b ℕ.+ c ≡⟨ ℕ.+-comm b c ⟩
  c ℕ.+ b ≡⟨ a+d≡c+b ⟨
  a ℕ.+ d ≡⟨ ℕ.+-comm a d ⟩
  d ℕ.+ a ∎
  where open ≡-Reasoning

+-inverseˡ : LeftInverse 0ℤ -_ _+_
+-inverseˡ (a ⊖ b) = trans (ℕ.+-identityʳ (b ℕ.+ a)) (ℕ.+-comm b a)

+-inverseʳ : RightInverse 0ℤ -_ _+_
+-inverseʳ (a ⊖ b) = trans (ℕ.+-identityʳ (a ℕ.+ b)) (ℕ.+-comm a b)

------------------------------------------------------------------------
-- Properties of -_ and _≤_

-‿anti-≤ : Antitonic₁ _≤_ _≤_ -_
-‿anti-≤ {a ⊖ b} {c ⊖ d} a+d≥c+b = begin
  b ℕ.+ c ≡⟨ ℕ.+-comm b c ⟩
  c ℕ.+ b ≤⟨ a+d≥c+b ⟩
  a ℕ.+ d ≡⟨ ℕ.+-comm a d ⟩
  d ℕ.+ a ∎
  where open ℕ.≤-Reasoning

------------------------------------------------------------------------
-- Algebraic properties of _*_

*-cong : Congruent₂ _*_
*-cong {a ⊖ b} {c ⊖ d} {e ⊖ f} {g ⊖ h} a+d≡c+b e+h≡g+f = ℕ.+-cancelʳ-≡ (d ℕ.* e) _ _ $ begin
  ((a ℕ.* e ℕ.+ b ℕ.* f) ℕ.+ (c ℕ.* h ℕ.+ d ℕ.* g)) ℕ.+ d ℕ.* e ≡⟨ ℕ.+-assoc (a ℕ.* e ℕ.+ b ℕ.* f) (c ℕ.* h ℕ.+ d ℕ.* g) (d ℕ.* e) ⟩
  (a ℕ.* e ℕ.+ b ℕ.* f) ℕ.+ ((c ℕ.* h ℕ.+ d ℕ.* g) ℕ.+ d ℕ.* e) ≡⟨ cong (a ℕ.* e ℕ.+ b ℕ.* f ℕ.+_) (ℕ.+-comm (c ℕ.* h ℕ.+ d ℕ.* g) (d ℕ.* e)) ⟩
  (a ℕ.* e ℕ.+ b ℕ.* f) ℕ.+ (d ℕ.* e ℕ.+ (c ℕ.* h ℕ.+ d ℕ.* g)) ≡⟨ medial (a ℕ.* e) (b ℕ.* f) (d ℕ.* e) (c ℕ.* h ℕ.+ d ℕ.* g) ⟩
  (a ℕ.* e ℕ.+ d ℕ.* e) ℕ.+ (b ℕ.* f ℕ.+ (c ℕ.* h ℕ.+ d ℕ.* g)) ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribʳ-+ e a d) (ℕ.+-comm (c ℕ.* h ℕ.+ d ℕ.* g) (b ℕ.* f)) ⟨
  (a ℕ.+ d) ℕ.* e ℕ.+ ((c ℕ.* h ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)       ≡⟨ cong (λ k → k ℕ.* e ℕ.+ ((c ℕ.* h ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)) a+d≡c+b ⟩
  (c ℕ.+ b) ℕ.* e ℕ.+ ((c ℕ.* h ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)       ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribʳ-+ e c b) (ℕ.+-assoc (c ℕ.* h) (d ℕ.* g) (b ℕ.* f)) ⟩
  (c ℕ.* e ℕ.+ b ℕ.* e) ℕ.+ (c ℕ.* h ℕ.+ (d ℕ.* g ℕ.+ b ℕ.* f)) ≡⟨ medial (c ℕ.* e) (b ℕ.* e) (c ℕ.* h) (d ℕ.* g ℕ.+ b ℕ.* f) ⟩
  (c ℕ.* e ℕ.+ c ℕ.* h) ℕ.+ (b ℕ.* e ℕ.+ (d ℕ.* g ℕ.+ b ℕ.* f)) ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribˡ-+ c e h) (ℕ.+-assoc (b ℕ.* e) (d ℕ.* g) (b ℕ.* f)) ⟨
  c ℕ.* (e ℕ.+ h) ℕ.+ ((b ℕ.* e ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)       ≡⟨ cong (λ k → c ℕ.* k ℕ.+ ((b ℕ.* e ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)) e+h≡g+f ⟩
  c ℕ.* (g ℕ.+ f) ℕ.+ ((b ℕ.* e ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)       ≡⟨ cong (ℕ._+ ((b ℕ.* e ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f)) (ℕ.*-distribˡ-+ c g f) ⟩
  (c ℕ.* g ℕ.+ c ℕ.* f) ℕ.+ ((b ℕ.* e ℕ.+ d ℕ.* g) ℕ.+ b ℕ.* f) ≡⟨ medial (c ℕ.* g) (c ℕ.* f) (b ℕ.* e ℕ.+ d ℕ.* g) (b ℕ.* f) ⟩
  (c ℕ.* g ℕ.+ (b ℕ.* e ℕ.+ d ℕ.* g)) ℕ.+ (c ℕ.* f ℕ.+ b ℕ.* f) ≡⟨ cong₂ ℕ._+_ (ℕ.+-assoc (c ℕ.* g) (b ℕ.* e) (d ℕ.* g)) (ℕ.*-distribʳ-+ f c b) ⟨
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ d ℕ.* g) ℕ.+ (c ℕ.+ b) ℕ.* f       ≡⟨ cong (λ k → ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ d ℕ.* g) ℕ.+ k ℕ.* f) a+d≡c+b ⟨
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ d ℕ.* g) ℕ.+ (a ℕ.+ d) ℕ.* f       ≡⟨ cong (c ℕ.* g ℕ.+ b ℕ.* e ℕ.+ d ℕ.* g ℕ.+_) (ℕ.*-distribʳ-+ f a d) ⟩
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ d ℕ.* g) ℕ.+ (a ℕ.* f ℕ.+ d ℕ.* f) ≡⟨ medial (c ℕ.* g ℕ.+ b ℕ.* e) (d ℕ.* g) (a ℕ.* f) (d ℕ.* f) ⟩
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ a ℕ.* f) ℕ.+ (d ℕ.* g ℕ.+ d ℕ.* f) ≡⟨ cong (((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ a ℕ.* f) ℕ.+_) (ℕ.*-distribˡ-+ d g f)  ⟨
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ a ℕ.* f) ℕ.+ d ℕ.* (g ℕ.+ f)       ≡⟨ cong (λ k → c ℕ.* g ℕ.+ b ℕ.* e ℕ.+ a ℕ.* f ℕ.+ d ℕ.* k) e+h≡g+f ⟨
  ((c ℕ.* g ℕ.+ b ℕ.* e) ℕ.+ a ℕ.* f) ℕ.+ d ℕ.* (e ℕ.+ h)       ≡⟨ cong₂ (λ j k → j ℕ.+ d ℕ.* k) (ℕ.+-assoc (c ℕ.* g) (b ℕ.* e) (a ℕ.* f)) (ℕ.+-comm e h) ⟩
  (c ℕ.* g ℕ.+ (b ℕ.* e ℕ.+ a ℕ.* f)) ℕ.+ d ℕ.* (h ℕ.+ e)       ≡⟨ cong₂ (λ j k → c ℕ.* g ℕ.+ j ℕ.+ k) (ℕ.+-comm (b ℕ.* e) (a ℕ.* f)) (ℕ.*-distribˡ-+ d h e) ⟩
  (c ℕ.* g ℕ.+ (a ℕ.* f ℕ.+ b ℕ.* e)) ℕ.+ (d ℕ.* h ℕ.+ d ℕ.* e) ≡⟨ medial (c ℕ.* g) (a ℕ.* f ℕ.+ b ℕ.* e) (d ℕ.* h) (d ℕ.* e) ⟩
  (c ℕ.* g ℕ.+ d ℕ.* h) ℕ.+ ((a ℕ.* f ℕ.+ b ℕ.* e) ℕ.+ d ℕ.* e) ≡⟨ ℕ.+-assoc (c ℕ.* g ℕ.+ d ℕ.* h) (a ℕ.* f ℕ.+ b ℕ.* e) (d ℕ.* e) ⟨
  ((c ℕ.* g ℕ.+ d ℕ.* h) ℕ.+ (a ℕ.* f ℕ.+ b ℕ.* e)) ℕ.+ d ℕ.* e ∎
  where
    open ≡-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup

*-assoc : Associative _*_
*-assoc (a ⊖ b) (c ⊖ d) (e ⊖ f) = cong₂ ℕ._+_ (lemma a b c d e f) (sym (lemma a b c d f e))
  where
    open ≡-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup
    lemma : ∀ u v w x y z → (u ℕ.* w ℕ.+ v ℕ.* x) ℕ.* y ℕ.+ (u ℕ.* x ℕ.+ v ℕ.* w) ℕ.* z
                          ≡ u ℕ.* (w ℕ.* y ℕ.+ x ℕ.* z) ℕ.+ v ℕ.* (w ℕ.* z ℕ.+ x ℕ.* y)
    lemma u v w x y z = begin
      (u ℕ.* w ℕ.+ v ℕ.* x) ℕ.* y ℕ.+ (u ℕ.* x ℕ.+ v ℕ.* w) ℕ.* z                     ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribʳ-+ y (u ℕ.* w) (v ℕ.* x)) (ℕ.*-distribʳ-+ z (u ℕ.* x) (v ℕ.* w)) ⟩
      ((u ℕ.* w) ℕ.* y ℕ.+ (v ℕ.* x) ℕ.* y) ℕ.+ ((u ℕ.* x) ℕ.* z ℕ.+ (v ℕ.* w) ℕ.* z) ≡⟨ cong₂ ℕ._+_ (cong₂ ℕ._+_ (ℕ.*-assoc u w y) (ℕ.*-assoc v x y)) (cong₂ ℕ._+_ (ℕ.*-assoc u x z) (ℕ.*-assoc v w z)) ⟩
      (u ℕ.* (w ℕ.* y) ℕ.+ v ℕ.* (x ℕ.* y)) ℕ.+ (u ℕ.* (x ℕ.* z) ℕ.+ v ℕ.* (w ℕ.* z)) ≡⟨ medial (u ℕ.* (w ℕ.* y)) (v ℕ.* (x ℕ.* y)) (u ℕ.* (x ℕ.* z)) (v ℕ.* (w ℕ.* z)) ⟩
      (u ℕ.* (w ℕ.* y) ℕ.+ u ℕ.* (x ℕ.* z)) ℕ.+ (v ℕ.* (x ℕ.* y) ℕ.+ v ℕ.* (w ℕ.* z)) ≡⟨ cong ((u ℕ.* (w ℕ.* y) ℕ.+ u ℕ.* (x ℕ.* z)) ℕ.+_) (ℕ.+-comm (v ℕ.* (x ℕ.* y)) (v ℕ.* (w ℕ.* z))) ⟩
      (u ℕ.* (w ℕ.* y) ℕ.+ u ℕ.* (x ℕ.* z)) ℕ.+ (v ℕ.* (w ℕ.* z) ℕ.+ v ℕ.* (x ℕ.* y)) ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribˡ-+ u (w ℕ.* y) (x ℕ.* z)) (ℕ.*-distribˡ-+ v (w ℕ.* z) (x ℕ.* y)) ⟨
      u ℕ.* (w ℕ.* y ℕ.+ x ℕ.* z) ℕ.+ v ℕ.* (w ℕ.* z ℕ.+ x ℕ.* y)                     ∎

*-zeroˡ : LeftZero 0ℤ _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero 0ℤ _*_
*-zeroʳ _ = ℕ.+-identityʳ _

*-identityˡ : LeftIdentity 1ℤ _*_
*-identityˡ (a ⊖ b) = cong₂ ℕ._+_ (lemma a) (sym (lemma b))
  where
    lemma : ∀ n → n ℕ.+ 0 ℕ.+ 0 ≡ n
    lemma n = trans (ℕ.+-identityʳ (n ℕ.+ 0)) (ℕ.+-identityʳ n)

*-identityʳ : RightIdentity 1ℤ _*_
*-identityʳ (a ⊖ b) = cong₂ ℕ._+_ l (sym r)
  where
    l : a ℕ.* 1 ℕ.+ b ℕ.* 0 ≡ a
    l = trans (cong₂ ℕ._+_ (ℕ.*-identityʳ a) (ℕ.*-zeroʳ b)) (ℕ.+-identityʳ a)
    r : a ℕ.* 0 ℕ.+ b ℕ.* 1 ≡ b
    r = trans (cong₂ ℕ._+_ (ℕ.*-zeroʳ a) (ℕ.*-identityʳ b)) (ℕ.+-identityˡ b)

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ (a ⊖ b) (c ⊖ d) (e ⊖ f) = cong₂ ℕ._+_ (lemma a b c d e f) (sym (lemma a b d c f e))
  where
    open ≡-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup
    lemma : ∀ u v w x y z → u ℕ.* (w ℕ.+ y) ℕ.+ v ℕ.* (x ℕ.+ z)
                            ≡ (u ℕ.* w ℕ.+ v ℕ.* x) ℕ.+ (u ℕ.* y ℕ.+ v ℕ.* z)
    lemma u v w x y z = begin
      u ℕ.* (w ℕ.+ y) ℕ.+ v ℕ.* (x ℕ.+ z)             ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribˡ-+ u w y) (ℕ.*-distribˡ-+ v x z) ⟩
      (u ℕ.* w ℕ.+ u ℕ.* y) ℕ.+ (v ℕ.* x ℕ.+ v ℕ.* z) ≡⟨ medial (u ℕ.* w) (u ℕ.* y) (v ℕ.* x) (v ℕ.* z) ⟩
      (u ℕ.* w ℕ.+ v ℕ.* x) ℕ.+ (u ℕ.* y ℕ.+ v ℕ.* z) ∎

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ (a ⊖ b) (c ⊖ d) (e ⊖ f) = cong₂ ℕ._+_ (lemma a b c d e f) (sym (lemma b a c d e f))
  where
    open ≡-Reasoning
    open CommSemigroupProps ℕ.+-commutativeSemigroup
    lemma : ∀ u v w x y z → (w ℕ.+ y) ℕ.* u ℕ.+ (x ℕ.+ z) ℕ.* v
                          ≡ (w ℕ.* u ℕ.+ x ℕ.* v) ℕ.+ (y ℕ.* u ℕ.+ z ℕ.* v)
    lemma u v w x y z = begin
      (w ℕ.+ y) ℕ.* u ℕ.+ (x ℕ.+ z) ℕ.* v             ≡⟨ cong₂ ℕ._+_ (ℕ.*-distribʳ-+ u w y) (ℕ.*-distribʳ-+ v x z) ⟩
      (w ℕ.* u ℕ.+ y ℕ.* u) ℕ.+ (x ℕ.* v ℕ.+ z ℕ.* v) ≡⟨ medial (w ℕ.* u) (y ℕ.* u) (x ℕ.* v) (z ℕ.* v) ⟩
      (w ℕ.* u ℕ.+ x ℕ.* v) ℕ.+ (y ℕ.* u ℕ.+ z ℕ.* v) ∎

*-comm : Commutative _*_
*-comm (a ⊖ b) (c ⊖ d) = cong₂ ℕ._+_ (cong₂ ℕ._+_ (ℕ.*-comm a c) (ℕ.*-comm b d)) (trans (ℕ.+-comm (c ℕ.* b) (d ℕ.* a)) (cong₂ ℕ._+_ (ℕ.*-comm d a) (ℕ.*-comm c b)))

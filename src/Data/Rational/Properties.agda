------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Properties where

open import Algebra.Consequences.Propositional
open import Algebra.Morphism
open import Algebra.Bundles
import Algebra.Morphism.MonoidMonomorphism as MonoidMonomorphisms
import Algebra.Morphism.GroupMonomorphism as GroupMonomorphisms
import Algebra.Morphism.RingMonomorphism as RingMonomorphisms
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Integer.Base as ℤ using (ℤ; ∣_∣; +_; -[1+_]; 0ℤ; _◃_)
open import Data.Integer.Coprimality using (coprime-divisor)
import Data.Integer.Properties as ℤ
open import Data.Integer.GCD using (gcd; gcd[i,j]≡0⇒i≡0; gcd[i,j]≡0⇒j≡0)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Nat.Coprimality as C using (Coprime; coprime?)
open import Data.Nat.Divisibility hiding (/-cong)
import Data.Nat.GCD as ℕ
import Data.Nat.DivMod as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base
open import Data.Rational.Unnormalised as ℚᵘ
  using (ℚᵘ; *≡*; *≤*; *<*) renaming (↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_; _≃_ to _≃ᵘ_; _≤_ to _≤ᵘ_; _<_ to _<ᵘ_)
import Data.Rational.Unnormalised.Properties as ℚᵘ
open import Data.Sum.Base
open import Data.Unit using (tt)
import Data.Sign as S
open import Function using (_∘_ ; _$_; Injective)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Morphism.Structures
import Relation.Binary.Morphism.OrderMonomorphism as OrderMonomorphisms
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Nullary.Decidable as Dec
  using (True; False; fromWitness; fromWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable as Dec using (True; fromWitness; map′)
open import Relation.Nullary.Product using (_×-dec_)

open import Algebra.Definitions {A = ℚ} _≡_
open import Algebra.Structures {A = ℚ} _≡_

private
  infix 4 _≢0
  _≢0 : ℕ → Set
  n ≢0 = False (n ℕ.≟ 0)

  recomputeCP : ∀ {n d} → .(Coprime n d) → Coprime n d
  recomputeCP {n} {d} c = recompute (coprime? n d) c

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

mkℚ-injective : ∀ {n₁ n₂ d₁ d₂} .{c₁ : Coprime ∣ n₁ ∣ (suc d₁)}
                                .{c₂ : Coprime ∣ n₂ ∣ (suc d₂)} →
                mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂ → n₁ ≡ n₂ × d₁ ≡ d₂
mkℚ-injective refl = refl , refl

infix 4 _≟_
_≟_ : Decidable {A = ℚ} _≡_
mkℚ n₁ d₁ _ ≟ mkℚ n₂ d₂ _ =
  map′ (λ { (refl , refl) → refl }) mkℚ-injective (n₁ ℤ.≟ n₂ ×-dec d₁ ℕ.≟ d₂)

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ℚ

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- mkℚ
------------------------------------------------------------------------

mkℚ-cong : ∀ {n₁ n₂ d₁ d₂}
           .{c₁ : Coprime ∣ n₁ ∣ (suc d₁)}
           .{c₂ : Coprime ∣ n₂ ∣ (suc d₂)} →
           n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
mkℚ-cong refl refl = refl

------------------------------------------------------------------------
-- mkℚ′
------------------------------------------------------------------------

mkℚ+-cong : ∀ {n₁ n₂ d₁ d₂} d₁≢0 d₂≢0
           .{c₁ : Coprime n₁ d₁}
           .{c₂ : Coprime n₂ d₂} →
           n₁ ≡ n₂ → d₁ ≡ d₂ →
           mkℚ+ n₁ d₁ {d₁≢0} c₁ ≡ mkℚ+ n₂ d₂ {d₂≢0} c₂
mkℚ+-cong _ _ refl refl = refl

↥-mkℚ+ : ∀ n d {d≢0} .{c : Coprime n d} → ↥ (mkℚ+ n d {d≢0} c) ≡ + n
↥-mkℚ+ n (suc d) = refl

↧-mkℚ+ : ∀ n d {d≢0} .{c : Coprime n d} → ↧ (mkℚ+ n d {d≢0} c) ≡ + d
↧-mkℚ+ n (suc d) = refl

------------------------------------------------------------------------
-- mkℚ*+
------------------------------------------------------------------------

mkℚ*+-cong : ∀ {n₁ n₂ d₁ d₂} d₁≢0 d₂≢0
             .{c₁ : Coprime (suc n₁) d₁}
             .{c₂ : Coprime (suc n₂) d₂} →
             n₁ ≡ n₂ → d₁ ≡ d₂ →
             mkℚ*+ n₁ d₁ {d₁≢0} c₁ ≡ mkℚ*+ n₂ d₂ {d₂≢0} c₂
mkℚ*+-cong _ _ refl refl = refl

↥-mkℚ*+ : ∀ n d {d≢0} .{c : Coprime (suc n) d} → ↥ (mkℚ*+ n d {d≢0} c) ≡ + (suc n)
↥-mkℚ*+ n (suc d) = refl

↧-mkℚ*+ : ∀ n d {d≢0} .{c : Coprime (suc n) d} → ↧ (mkℚ*+ n d {d≢0} c) ≡ + d
↧-mkℚ*+ n (suc d) = refl

------------------------------------------------------------------------
-- Numerator and denominator equality
------------------------------------------------------------------------

≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = refl

≃⇒≡ : _≃_ ⇒ _≡_
≃⇒≡ {x = mkℚ n₁ d₁ c₁} {y = mkℚ n₂ d₂ c₂} eq = helper
  where
  open ≡-Reasoning

  1+d₁∣1+d₂ : suc d₁ ∣ suc d₂
  1+d₁∣1+d₂ = coprime-divisor (+ suc d₁) n₁ (+ suc d₂)
    (C.sym (recomputeCP c₁)) $
    divides ∣ n₂ ∣ $ begin
      ∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ cong ∣_∣ eq ⟩
      ∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ ℤ.abs-*-commute n₂ (+ suc d₁) ⟩
      ∣ n₂ ∣ ℕ.* suc d₁    ∎

  1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
  1+d₂∣1+d₁ = coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
    (C.sym (recomputeCP c₂)) $
    divides ∣ n₁ ∣ (begin
      ∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ cong ∣_∣ (sym eq) ⟩
      ∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ ℤ.abs-*-commute n₁ (+ suc d₂) ⟩
      ∣ n₁ ∣ ℕ.* suc d₂    ∎)

  helper : mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
  helper with ∣-antisym 1+d₁∣1+d₂ 1+d₂∣1+d₁
  ... | refl with ℤ.*-cancelʳ-≡ n₁ n₂ (+ suc d₁) (λ ()) eq
  ...   | refl = refl

------------------------------------------------------------------------
-- Properties of normalize
------------------------------------------------------------------------

normalize-coprime : ∀ {n d-1} .(c : Coprime n (suc d-1)) →
                    normalize n (suc d-1) ≡ mkℚ (+ n) d-1 c
normalize-coprime {n} {d-1} c = begin
  normalize n d              ≡⟨⟩
  mkℚ+ (n ℕ./ g) (d ℕ./ g) _ ≡⟨ mkℚ+-cong n/g≢0 d/1≢0 {c₂ = c₂} (ℕ./-congʳ {n≢0 = g≢0} g≡1) (ℕ./-congʳ {n≢0 = g≢0} g≡1) ⟩
  mkℚ+ (n ℕ./ 1) (d ℕ./ 1) _ ≡⟨ mkℚ+-cong d/1≢0 _ {c₂ = c} (ℕ.n/1≡n n) (ℕ.n/1≡n d) ⟩
  mkℚ+ n d _                 ≡⟨⟩
  mkℚ (+ n) d-1 _            ∎
  where
  open ≡-Reasoning; d = suc d-1; g = ℕ.gcd n d
  c′ = recomputeCP c
  c₂ : Coprime (n ℕ./ 1) (d ℕ./ 1)
  c₂ = subst₂ Coprime (sym (ℕ.n/1≡n n)) (sym (ℕ.n/1≡n d)) c′
  g≡1 = C.coprime⇒gcd≡1 c′
  g≢0   = fromWitnessFalse (ℕ.gcd[m,n]≢0 n d (inj₂ λ()))
  n/g≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 n d {_} {g≢0})
  d/1≢0 = fromWitnessFalse (subst (_≢ 0) (sym (ℕ.n/1≡n d)) λ())

↥-normalize : ∀ i n {n≢0} → ↥ (normalize i n {n≢0}) ℤ.* gcd (+ i) (+ n) ≡ + i
↥-normalize i n@(suc n-1) = begin
  ↥ (normalize i n) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↥-mkℚ+ _ (n ℕ./ g) {n/g≢0}) ⟩
  + (i ℕ./ g)       ℤ.* + g  ≡⟨⟩
  S.+ ◃ i ℕ./ g     ℕ.* g    ≡⟨ cong (S.+ ◃_) (ℕ.m/n*n≡m (ℕ.gcd[m,n]∣m i n)) ⟩
  S.+ ◃ i                    ≡⟨ ℤ.+◃n≡+n i ⟩
  + i                        ∎
  where
  open ≡-Reasoning; g = ℕ.gcd i n
  g≢0   = fromWitnessFalse (ℕ.gcd[m,n]≢0 i n (inj₂ λ()))
  n/g≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 i n {_} {g≢0})

↧-normalize : ∀ i n {n≢0} → ↧ (normalize i n {n≢0}) ℤ.* gcd (+ i) (+ n) ≡ + n
↧-normalize i n@(suc n-1) = begin
  ↧ (normalize i n) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↧-mkℚ+ _ (n ℕ./ g) {n/g≢0}) ⟩
  + (n ℕ./ g)       ℤ.* + g  ≡⟨⟩
  S.+ ◃ n ℕ./ g     ℕ.* g    ≡⟨ cong (S.+ ◃_) (ℕ.m/n*n≡m (ℕ.gcd[m,n]∣n i n)) ⟩
  S.+ ◃ n                    ≡⟨ ℤ.+◃n≡+n n ⟩
  + n                        ∎
  where
  open ≡-Reasoning; g = ℕ.gcd i n
  g≢0   = fromWitnessFalse (ℕ.gcd[m,n]≢0 i n (inj₂ λ()))
  n/g≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 i n {_} {g≢0})

------------------------------------------------------------------------
-- Properties of toℚ/fromℚ
------------------------------------------------------------------------

toℚᵘ-cong : toℚᵘ Preserves _≡_ ⟶ _≃ᵘ_
toℚᵘ-cong refl = *≡* refl

toℚᵘ-injective : Injective _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-injective (*≡* eq) = ≃⇒≡ eq

toℚᵘ-isRelHomomorphism : IsRelHomomorphism _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-isRelHomomorphism = record
  { cong = toℚᵘ-cong
  }

toℚᵘ-isRelMonomorphism : IsRelMonomorphism _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-isRelMonomorphism = record
  { isHomomorphism = toℚᵘ-isRelHomomorphism
  ; injective      = toℚᵘ-injective
  }

fromℚᵘ-toℚᵘ : ∀ p → fromℚᵘ (toℚᵘ p) ≡ p
fromℚᵘ-toℚᵘ (mkℚ (+ n)      d-1 c) = normalize-coprime c
fromℚᵘ-toℚᵘ (mkℚ (-[1+ n ]) d-1 c) = cong (-_) (normalize-coprime c)

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

drop-*≤* : ∀ {p q} → p ≤ q → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p)
drop-*≤* (*≤* pq≤qp) = pq≤qp

------------------------------------------------------------------------
-- toℚᵘ is an order monomorphism

toℚᵘ-mono-≤ : ∀ {p q} → p ≤ q → toℚᵘ p ≤ᵘ toℚᵘ q
toℚᵘ-mono-≤ (*≤* p≤q) = *≤* p≤q

toℚᵘ-cancel-≤ : ∀ {p q} → toℚᵘ p ≤ᵘ toℚᵘ q → p ≤ q
toℚᵘ-cancel-≤ (*≤* p≤q) = *≤* p≤q

toℚᵘ-isOrderHomomorphism-≤ : IsOrderHomomorphism _≡_ _≃ᵘ_ _≤_ _≤ᵘ_ toℚᵘ
toℚᵘ-isOrderHomomorphism-≤ = record
  { cong = toℚᵘ-cong
  ; mono = toℚᵘ-mono-≤
  }

toℚᵘ-isOrderMonomorphism-≤ : IsOrderMonomorphism _≡_ _≃ᵘ_ _≤_ _≤ᵘ_ toℚᵘ
toℚᵘ-isOrderMonomorphism-≤ = record
  { isOrderHomomorphism = toℚᵘ-isOrderHomomorphism-≤
  ; injective           = toℚᵘ-injective
  ; cancel              = toℚᵘ-cancel-≤
  }

private
  module ≤-Monomorphism = OrderMonomorphisms toℚᵘ-isOrderMonomorphism-≤

------------------------------------------------------------------------
-- Relational properties

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = *≤* ℤ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans = ≤-Monomorphism.trans ℚᵘ.≤-trans

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = ≤-Monomorphism.antisym ℚᵘ.≤-antisym

≤-total : Total _≤_
≤-total = ≤-Monomorphism.total ℚᵘ.≤-total

infix 4 _≤?_
_≤?_ : Decidable _≤_
_≤?_ = ≤-Monomorphism.dec ℚᵘ._≤?_

≤-irrelevant : Irrelevant _≤_
≤-irrelevant (*≤* p≤q₁) (*≤* p≤q₂) = cong *≤* (ℤ.≤-irrelevant p≤q₁ p≤q₂)

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = ≤-Monomorphism.isPreorder ℚᵘ.≤-isPreorder

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = ≤-Monomorphism.isPartialOrder ℚᵘ.≤-isPartialOrder

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = ≤-Monomorphism.isTotalOrder ℚᵘ.≤-isTotalOrder

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = ≤-Monomorphism.isDecTotalOrder ℚᵘ.≤-isDecTotalOrder


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
-- toℚᵘ is an isomorphism

toℚᵘ-mono-< : ∀ {p q} → p < q → toℚᵘ p <ᵘ toℚᵘ q
toℚᵘ-mono-< (*<* p<q) = *<* p<q

toℚᵘ-cancel-< : ∀ {p q} → toℚᵘ p <ᵘ toℚᵘ q → p < q
toℚᵘ-cancel-< (*<* p<q) = *<* p<q

toℚᵘ-isOrderHomomorphism-< : IsOrderHomomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ
toℚᵘ-isOrderHomomorphism-< = record
  { cong = toℚᵘ-cong
  ; mono = toℚᵘ-mono-<
  }

toℚᵘ-isOrderMonomorphism-< : IsOrderMonomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ
toℚᵘ-isOrderMonomorphism-< = record
  { isOrderHomomorphism = toℚᵘ-isOrderHomomorphism-<
  ; injective           = toℚᵘ-injective
  ; cancel              = toℚᵘ-cancel-<
  }

private
  module <-Monomorphism = OrderMonomorphisms toℚᵘ-isOrderMonomorphism-<

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

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (*<* p<p) = ℤ.<-irrefl refl p<p

<-asym : Asymmetric _<_
<-asym (*<* p<q) (*<* q<p) = ℤ.<-asym p<q q<p

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans p<q q≤r =
  toℚᵘ-cancel-< $ ℚᵘ.<-≤-trans (toℚᵘ-mono-< p<q)
                               (toℚᵘ-mono-≤ q≤r)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans p≤q q<r =
  toℚᵘ-cancel-< $ ℚᵘ.≤-<-trans (toℚᵘ-mono-≤ p≤q)
                               (toℚᵘ-mono-< q<r)

<-trans : Transitive _<_
<-trans = <-Monomorphism.trans ℚᵘ.<-trans

infix 4 _<?_
_<?_ : Decidable _<_
_<?_ = <-Monomorphism.dec ℚᵘ._<?_

<-cmp : Trichotomous _≡_ _<_
<-cmp = <-Monomorphism.compare ℚᵘ.<-cmp

<-irrelevant : Irrelevant _<_
<-irrelevant (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤ.<-irrelevant p<q₁ p<q₂)

<-respʳ-≡ : _<_ Respectsʳ _≡_
<-respʳ-≡ = subst (_ <_)

<-respˡ-≡ : _<_ Respectsˡ _≡_
<-respˡ-≡ = subst (_< _)

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = <-respʳ-≡ , <-respˡ-≡

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = <-Monomorphism.isStrictPartialOrder ℚᵘ.<-isStrictPartialOrder

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = <-Monomorphism.isStrictTotalOrder ℚᵘ.<-isStrictTotalOrder

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Other properties of _<_

p≮p : ∀ {p} → p ≮ p
p≮p {p} = <-irrefl refl

>-irrefl : Irreflexive _≡_ _>_
>-irrefl = <-irrefl ∘ sym

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
    hiding (step-≈; step-≈˘)

------------------------------------------------------------------------
-- Positivity is preserved
------------------------------------------------------------------------

pos-toℚᵘ : ∀ {p} → p > 0ℚ → ℚᵘ.pos (toℚᵘ p)
pos-toℚᵘ = ℚᵘ.>0⇒pos ∘ toℚᵘ-mono-<

non-neg-toℚᵘ : ∀ {p} → p ≥ 0ℚ → ℚᵘ.non-neg (toℚᵘ p)
non-neg-toℚᵘ = ℚᵘ.≥0⇒non-neg ∘ toℚᵘ-mono-≤

------------------------------------------------------------------------
-- Properties of -_
------------------------------------------------------------------------

↥-neg : ∀ p → ↥ (- p) ≡ ℤ.- (↥ p)
↥-neg (mkℚ -[1+ _ ] _ _) = refl
↥-neg (mkℚ +0       _ _) = refl
↥-neg (mkℚ +[1+ _ ] _ _) = refl

↧-neg : ∀ p → ↧ (- p) ≡ ↧ p
↧-neg (mkℚ -[1+ _ ] _ _) = refl
↧-neg (mkℚ +0       _ _) = refl
↧-neg (mkℚ +[1+ _ ] _ _) = refl

denominator-1-neg : ∀ p → ℚ.denominator-1 (- p) ≡ ℚ.denominator-1 p
denominator-1-neg = ℕ.suc-injective ∘ ℤ.+-injective ∘ ↧-neg

------------------------------------------------------------------------
-- Properties of _/_
------------------------------------------------------------------------

↥-/ : ∀ i n {n≢0} → ↥ (i / n) {n≢0} ℤ.* gcd i (+ n) ≡ i
↥-/ (+ m)    (suc n) = ↥-normalize m (suc n)
↥-/ -[1+ m ] (suc n) = begin-equality
  ↥ (- norm)   ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↥-neg norm) ⟩
  ℤ.- (↥ norm) ℤ.* + g  ≡⟨ sym (ℤ.neg-distribˡ-* (↥ norm) (+ g)) ⟩
  ℤ.- (↥ norm  ℤ.* + g) ≡⟨ cong (ℤ.-_) (↥-normalize (suc m) (suc n)) ⟩
  S.- ◃ suc m           ≡⟨⟩
  -[1+ m ]              ∎
  where
  open ℤ.≤-Reasoning
  g = ℕ.gcd (suc m) (suc n)
  norm = normalize (suc m) (suc n)

↧-/ : ∀ i n {n≢0} → ↧ (i / n) {n≢0} ℤ.* gcd i (+ n) ≡ + n
↧-/ (+ m)    (suc n) = ↧-normalize m (suc n)
↧-/ -[1+ m ] (suc n) = begin-equality
  ↧ (- norm) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↧-neg norm) ⟩
  ↧ norm     ℤ.* + g  ≡⟨ ↧-normalize (suc m) (suc n) ⟩
  + (suc n)           ∎
  where
  open ℤ.≤-Reasoning
  g = ℕ.gcd (suc m) (suc n)
  norm = normalize (suc m) (suc n)

↥p/↧p≡p : ∀ p → ↥ p / ↧ₙ p ≡ p
↥p/↧p≡p (mkℚ (+ n)    d-1 prf) = normalize-coprime prf
↥p/↧p≡p (mkℚ -[1+ n ] d-1 prf) = cong (-_) (normalize-coprime prf)

0/n≡0 : ∀ n {n≢0} → (0ℤ / n) {n≢0} ≡ 0ℚ
0/n≡0 n@(suc n-1) {n≢0} = mkℚ+-cong n/n≢0 _ {c₂ = 0-cop-1} (ℕ.0/n≡0 (ℕ.gcd 0 n)) (ℕ.n/n≡1 n)
  where
  n/n≢0 = subst _≢0 (sym (ℕ.n/n≡1 n)) _
  0-cop-1 = C.sym (C.1-coprimeTo 0)

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

private
  ↥+ᵘ : ℚ → ℚ → ℤ
  ↥+ᵘ p q = ↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p

  ↧+ᵘ : ℚ → ℚ → ℤ
  ↧+ᵘ p q = ↧ p ℤ.* ↧ q

  +-nf : ℚ → ℚ → ℤ
  +-nf p q = gcd (↥+ᵘ p q) (↧+ᵘ p q)

↥-+ : ∀ p q → ↥ (p + q) ℤ.* +-nf p q ≡ ↥+ᵘ p q
↥-+ p q = ↥-/ (↥+ᵘ p q) (↧ₙ p ℕ.* ↧ₙ q)

↧-+ : ∀ p q → ↧ (p + q) ℤ.* +-nf p q ≡ ↧+ᵘ p q
↧-+ p q = ↧-/ (↥+ᵘ p q) (↧ₙ p ℕ.* ↧ₙ q)

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-rawMonoid : RawMonoid 0ℓ 0ℓ
+-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℚ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℚ
  ; _⁻¹ = -_
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_  = -_
  ; 0#  = 0ℚ
  ; 1#  = 1ℚ
  }

------------------------------------------------------------------------
-- Monomorphic to unnormalised _+_

open Definitions ℚ ℚᵘ ℚᵘ._≃_

toℚᵘ-homo-+ : Homomorphic₂ toℚᵘ _+_ ℚᵘ._+_
toℚᵘ-homo-+ p q with +-nf p q ℤ.≟ 0ℤ
... | yes nf[p,q]≡0 = *≡* (begin
  ↥ (p + q) ℤ.* ↧+ᵘ p q   ≡⟨ cong (ℤ._* ↧+ᵘ p q) eq ⟩
  0ℤ        ℤ.* ↧+ᵘ p q   ≡⟨⟩
  0ℤ        ℤ.* ↧ (p + q) ≡⟨ cong (ℤ._* ↧ (p + q)) (sym eq2) ⟩
  ↥+ᵘ p q   ℤ.* ↧ (p + q) ∎)
  where
  open ≡-Reasoning
  eq2 : ↥+ᵘ p q ≡ 0ℤ
  eq2 = gcd[i,j]≡0⇒i≡0 (↥+ᵘ p q) (↧+ᵘ p q) nf[p,q]≡0

  eq : ↥ (p + q) ≡ 0ℤ
  eq rewrite eq2 = cong ↥_ (0/n≡0 (↧ₙ p ℕ.* ↧ₙ q))

... | no  nf[p,q]≢0 = *≡* (ℤ.*-cancelʳ-≡ _ _ (+-nf p q) nf[p,q]≢0 (begin
  ↥ (p + q) ℤ.* ↧+ᵘ p q    ℤ.* +-nf p q   ≡⟨ xy∙z≈xz∙y (↥ (p + q)) _ _ ⟩
  ↥ (p + q) ℤ.* +-nf p q   ℤ.* ↧+ᵘ p q    ≡⟨ cong (ℤ._* ↧+ᵘ p q) (↥-+ p q) ⟩
  ↥+ᵘ p q   ℤ.* ↧+ᵘ p q                   ≡⟨ cong (↥+ᵘ p q ℤ.*_) (sym (↧-+ p q)) ⟩
  ↥+ᵘ p q   ℤ.* (↧ (p + q) ℤ.* +-nf p q)  ≡⟨ x∙yz≈xy∙z (↥+ᵘ p q) _ _ ⟩
  ↥+ᵘ p q   ℤ.* ↧ (p + q)  ℤ.* +-nf p q   ∎))
  where open ≡-Reasoning; open CommSemigroupProperties ℤ.*-commutativeSemigroup

toℚᵘ-isMagmaHomomorphism-+ : IsMagmaHomomorphism +-rawMagma ℚᵘ.+-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-+ = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; homo              = toℚᵘ-homo-+
  }

toℚᵘ-isMonoidHomomorphism-+ : IsMonoidHomomorphism +-rawMonoid ℚᵘ.+-rawMonoid toℚᵘ
toℚᵘ-isMonoidHomomorphism-+ = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-+
  ; ε-homo              = ℚᵘ.≃-refl
  }

toℚᵘ-isMonoidMonomorphism-+ : IsMonoidMonomorphism +-rawMonoid ℚᵘ.+-rawMonoid toℚᵘ
toℚᵘ-isMonoidMonomorphism-+ = record
  { isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-+
  ; injective            = toℚᵘ-injective
  }

------------------------------------------------------------------------
-- Monomorphic to unnormalised -_

toℚᵘ-homo‿- : Homomorphic₁ toℚᵘ (-_) (ℚᵘ.-_)
toℚᵘ-homo‿- (mkℚ +0       _ _) = *≡* refl
toℚᵘ-homo‿- (mkℚ +[1+ _ ] _ _) = *≡* refl
toℚᵘ-homo‿- (mkℚ -[1+ _ ] _ _) = *≡* refl

toℚᵘ-isGroupHomomorphism-+ : IsGroupHomomorphism +-0-rawGroup ℚᵘ.+-0-rawGroup toℚᵘ
toℚᵘ-isGroupHomomorphism-+ = record
  { isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-+
  ; ⁻¹-homo              = toℚᵘ-homo‿-
  }

toℚᵘ-isGroupMonomorphism-+ : IsGroupMonomorphism +-0-rawGroup ℚᵘ.+-0-rawGroup toℚᵘ
toℚᵘ-isGroupMonomorphism-+ = record
  { isGroupHomomorphism = toℚᵘ-isGroupHomomorphism-+
  ; injective           = toℚᵘ-injective
  }

neg-mono-<-> : -_ Preserves _<_ ⟶ _>_
neg-mono-<-> {p} {q} p<q = toℚᵘ-cancel-< $ begin-strict
  toℚᵘ (- q)    ≡⟨ cong₂ ℚᵘ.mkℚᵘ (↥-neg q) (denominator-1-neg q) ⟩
  ℚᵘ.- (toℚᵘ q) <⟨ ℚᵘ.neg-mono-<-> (toℚᵘ-mono-< p<q) ⟩
  ℚᵘ.- (toℚᵘ p) ≡⟨ sym (cong₂ ℚᵘ.mkℚᵘ (↥-neg p) (denominator-1-neg p)) ⟩
  toℚᵘ (- p)    ∎
  where open ℚᵘ.≤-Reasoning

------------------------------------------------------------------------
-- Algebraic properties

private
  module +-Monomorphism = GroupMonomorphisms toℚᵘ-isGroupMonomorphism-+

+-comm : Commutative _+_
+-comm = +-Monomorphism.comm ℚᵘ.+-isMagma ℚᵘ.+-comm

+-identity : Identity 0ℚ _+_
+-identity = +-Monomorphism.identity ℚᵘ.+-isMagma ℚᵘ.+-identity

+-identityˡ : LeftIdentity 0ℚ _+_
+-identityˡ = proj₁ +-identity

+-identityʳ : RightIdentity 0ℚ _+_
+-identityʳ = proj₂ +-identity

+-inverse : Inverse 0ℚ -_ _+_
+-inverse = +-Monomorphism.inverse ℚᵘ.+-isMagma ℚᵘ.+-inverse

+-inverseˡ : LeftInverse 0ℚ -_ _+_
+-inverseˡ = proj₁ +-inverse

+-inverseʳ : RightInverse 0ℚ -_ _+_
+-inverseʳ = proj₂ +-inverse

-‿cong :  Congruent₁ (-_)
-‿cong = +-Monomorphism.⁻¹-cong ℚᵘ.+-isMagma ℚᵘ.-‿cong

------------------------------------------------------------------------
-- properties of _+_ and _≤_

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {p} {q} {r} {s} p≤q r≤s  = toℚᵘ-cancel-≤ $ begin
  toℚᵘ (p + r)       ≈⟨ toℚᵘ-homo-+ p r ⟩
  toℚᵘ p ℚᵘ.+ toℚᵘ r ≤⟨ ℚᵘ.+-mono-≤ (toℚᵘ-mono-≤ p≤q) (toℚᵘ-mono-≤ r≤s) ⟩
  toℚᵘ q ℚᵘ.+ toℚᵘ s ≈⟨ ℚᵘ.≃-sym (toℚᵘ-homo-+ q s) ⟩
  toℚᵘ (q + s)       ∎ where open ℚᵘ.≤-Reasoning

+-monoˡ-≤ : ∀ r → (_+ r) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ r p≤q = +-mono-≤ p≤q (≤-refl {x = r})

+-monoʳ-≤ : ∀ r → (_+_ r) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ r = +-mono-≤ (≤-refl {x = r})

≤-steps : ∀ {p q} r {r≥0 : r ≥ 0ℚ} → p ≤ q → p ≤ r + q
≤-steps {p} {q} r {r≥0} p≤q = subst (_≤ r + q) (+-identityˡ p) (+-mono-≤ r≥0 p≤q)

p≤p+q : ∀ q {q≥0 : q ≥ 0ℚ} {p} → p ≤ p + q
p≤p+q q {q≥0} {p} = subst (_≤ p + q) (+-identityʳ p) (+-monoʳ-≤ p q≥0)

p≤q+p : ∀ p {p≥0 : p ≥ 0ℚ} {q} → q ≤ p + q
p≤q+p p {p≥0} {q} rewrite +-comm p q = p≤p+q p {p≥0}

------------------------------------------------------------------------
-- properties of _+_ and _<_

+-monoʳ-< : ∀ r → (_+_ r) Preserves _<_ ⟶ _<_
+-monoʳ-< r {p} {q} p<q = toℚᵘ-cancel-< $ begin-strict
  toℚᵘ (r + p)       ≈⟨ toℚᵘ-homo-+ r p ⟩
  toℚᵘ r ℚᵘ.+ toℚᵘ p <⟨ ℚᵘ.+-monoʳ-< (toℚᵘ r) (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ r ℚᵘ.+ toℚᵘ q ≈⟨ ℚᵘ.≃-sym (toℚᵘ-homo-+ r q) ⟩
  toℚᵘ (r + q)       ∎ where open ℚᵘ.≤-Reasoning

+-monoˡ-< : ∀ r → (_+ r) Preserves _<_ ⟶ _<_
+-monoˡ-< r {p} {q} rewrite +-comm p r | +-comm q r = +-monoʳ-< r

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {p} {q} {u} {v} p<q u<v = <-trans (+-monoˡ-< u p<q) (+-monoʳ-< q u<v)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {p} {q} {r} p≤q q<r = ≤-<-trans (+-monoˡ-≤ r p≤q) (+-monoʳ-< q q<r)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {p} {q} {r} p<q q≤r = <-≤-trans (+-monoˡ-< r p<q) (+-monoʳ-≤ q q≤r)

------------------------------------------------------------------------
-- Structures

+-isMagma : IsMagma _+_
+-isMagma = +-Monomorphism.isMagma ℚᵘ.+-isMagma

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = +-Monomorphism.isSemigroup ℚᵘ.+-isSemigroup

+-0-isMonoid : IsMonoid _+_ 0ℚ
+-0-isMonoid = +-Monomorphism.isMonoid ℚᵘ.+-0-isMonoid

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0ℚ
+-0-isCommutativeMonoid = +-Monomorphism.isCommutativeMonoid ℚᵘ.+-0-isCommutativeMonoid

+-0-isGroup : IsGroup _+_ 0ℚ (-_)
+-0-isGroup = +-Monomorphism.isGroup ℚᵘ.+-0-isGroup

+-0-isAbelianGroup : IsAbelianGroup _+_ 0ℚ (-_)
+-0-isAbelianGroup = +-Monomorphism.isAbelianGroup ℚᵘ.+-0-isAbelianGroup

------------------------------------------------------------------------
-- Packages

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

private
  *-nf : ℚ → ℚ → ℤ
  *-nf p q = gcd (↥ p ℤ.* ↥ q) (↧ p ℤ.* ↧ q)

↥-* : ∀ p q → ↥ (p * q) ℤ.* *-nf p q ≡ ↥ p ℤ.* ↥ q
↥-* p q = ↥-/ (↥ p ℤ.* ↥ q) (↧ₙ p ℕ.* ↧ₙ q)

↧-* : ∀ p q → ↧ (p * q) ℤ.* *-nf p q ≡ ↧ p ℤ.* ↧ q
↧-* p q = ↧-/ (↥ p ℤ.* ↥ q) (↧ₙ p ℕ.* ↧ₙ q)

------------------------------------------------------------------------
-- Raw bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-rawMonoid : RawMonoid 0ℓ 0ℓ
*-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε   = 1ℚ
  }

------------------------------------------------------------------------
-- Monomorphic to unnormalised _*_

toℚᵘ-homo-* : Homomorphic₂ toℚᵘ _*_ ℚᵘ._*_
toℚᵘ-homo-* p q with *-nf p q ℤ.≟ 0ℤ
... | yes nf[p,q]≡0 = *≡* (begin
  ↥ (p * q)     ℤ.* (↧ p ℤ.* ↧ q) ≡⟨ cong (ℤ._* (↧ p ℤ.* ↧ q)) eq ⟩
  0ℤ            ℤ.* (↧ p ℤ.* ↧ q) ≡⟨⟩
  0ℤ            ℤ.* ↧ (p * q)     ≡⟨ cong (ℤ._* ↧ (p * q)) (sym eq2) ⟩
  (↥ p ℤ.* ↥ q) ℤ.* ↧ (p * q)     ∎)
  where
  open ≡-Reasoning
  eq2 : ↥ p ℤ.* ↥ q ≡ 0ℤ
  eq2 = gcd[i,j]≡0⇒i≡0 (↥ p ℤ.* ↥ q) (↧ p ℤ.* ↧ q) nf[p,q]≡0

  eq : ↥ (p * q) ≡ 0ℤ
  eq rewrite eq2 = cong ↥_ (0/n≡0 (↧ₙ p ℕ.* ↧ₙ q))
... | no  nf[p,q]≢0 = *≡* (ℤ.*-cancelʳ-≡ _ _ (*-nf p q) nf[p,q]≢0 (begin
  ↥ (p * q)     ℤ.* (↧ p ℤ.* ↧ q) ℤ.* *-nf p q ≡⟨ xy∙z≈xz∙y (↥ (p * q)) _ _ ⟩
  ↥ (p * q)     ℤ.* *-nf p q ℤ.* (↧ p ℤ.* ↧ q) ≡⟨ cong (ℤ._* (↧ p ℤ.* ↧ q)) (↥-* p q) ⟩
  (↥ p ℤ.* ↥ q) ℤ.* (↧ p ℤ.* ↧ q)              ≡⟨ cong ((↥ p ℤ.* ↥ q) ℤ.*_) (sym (↧-* p q)) ⟩
  (↥ p ℤ.* ↥ q) ℤ.* (↧ (p * q) ℤ.* *-nf p q)   ≡⟨ x∙yz≈xy∙z (↥ p ℤ.* ↥ q) _ _ ⟩
  (↥ p ℤ.* ↥ q) ℤ.* ↧ (p * q)  ℤ.* *-nf p q    ∎))
  where open ≡-Reasoning; open CommSemigroupProperties ℤ.*-commutativeSemigroup

toℚᵘ-isMagmaHomomorphism-* : IsMagmaHomomorphism *-rawMagma ℚᵘ.*-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-* = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; homo              = toℚᵘ-homo-*
  }

toℚᵘ-isMonoidHomomorphism-* : IsMonoidHomomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ
toℚᵘ-isMonoidHomomorphism-* = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-*
  ; ε-homo              = ℚᵘ.≃-refl
  }

toℚᵘ-isMonoidMonomorphism-* : IsMonoidMonomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ
toℚᵘ-isMonoidMonomorphism-* = record
  { isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-*
  ; injective            = toℚᵘ-injective
  }

toℚᵘ-isRingHomomorphism-+-* : IsRingHomomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ
toℚᵘ-isRingHomomorphism-+-* = record
  { +-isGroupHomomorphism  = toℚᵘ-isGroupHomomorphism-+
  ; *-isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-*
  }

toℚᵘ-isRingMonomorphism-+-* : IsRingMonomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ
toℚᵘ-isRingMonomorphism-+-* = record
  { isRingHomomorphism = toℚᵘ-isRingHomomorphism-+-*
  ; injective          = toℚᵘ-injective
  }

------------------------------------------------------------------------
-- Algebraic properties

private
  module *-Monomorphism = RingMonomorphisms toℚᵘ-isRingMonomorphism-+-*

*-assoc : Associative _*_
*-assoc = *-Monomorphism.*-assoc ℚᵘ.*-isMagma ℚᵘ.*-assoc

*-comm : Commutative _*_
*-comm = *-Monomorphism.*-comm ℚᵘ.*-isMagma ℚᵘ.*-comm

*-identity : Identity 1ℚ _*_
*-identity = *-Monomorphism.*-identity ℚᵘ.*-isMagma ℚᵘ.*-identity

*-identityˡ : LeftIdentity 1ℚ _*_
*-identityˡ = proj₁ *-identity

*-identityʳ : RightIdentity 1ℚ _*_
*-identityʳ = proj₂ *-identity

*-zero : Zero 0ℚ _*_
*-zero = *-Monomorphism.zero ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-zero

*-zeroˡ : LeftZero 0ℚ _*_
*-zeroˡ = proj₁ *-zero

*-zeroʳ : RightZero 0ℚ _*_
*-zeroʳ = proj₂ *-zero

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-Monomorphism.distrib ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distrib-+

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = proj₁ *-distrib-+

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = proj₂ *-distrib-+

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-cancelʳ-≤-pos : ∀ r {r>0 : r > 0ℚ} → ∀ {p q} → p * r ≤ q * r → p ≤ q
*-cancelʳ-≤-pos r {r>0} {p} {q} p*r≤q*r = toℚᵘ-cancel-≤ $
  ℚᵘ.*-cancelʳ-≤-pos (pos-toℚᵘ r>0) $ begin
  toℚᵘ p ℚᵘ.* toℚᵘ r ≈⟨ ℚᵘ.≃-sym (toℚᵘ-homo-* p r) ⟩
  toℚᵘ (p * r)       ≤⟨ toℚᵘ-mono-≤ p*r≤q*r ⟩
  toℚᵘ (q * r)       ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r ∎ where open ℚᵘ.≤-Reasoning

*-cancelˡ-≤-pos : ∀ r {r>0 : r > 0ℚ} {p q} → r * p ≤ r * q → p ≤ q
*-cancelˡ-≤-pos r {r>0} {p} {q}
  rewrite *-comm r p | *-comm r q = *-cancelʳ-≤-pos r {r>0}

*-monoˡ-≤-non-neg : ∀ r {r≥0 : r ≥ 0ℚ} → (_* r) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-non-neg r {r≥0} {p} {q} p≤q = toℚᵘ-cancel-≤ $ begin
  toℚᵘ (p * r)       ≈⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r ≤⟨ ℚᵘ.*-monoˡ-≤-non-neg (non-neg-toℚᵘ r≥0) (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r ≈⟨ (ℚᵘ.≃-sym $ toℚᵘ-homo-* q r) ⟩
  toℚᵘ (q * r)       ∎ where open ℚᵘ.≤-Reasoning

*-monoʳ-≤-non-neg : ∀ r {r≥0 : r ≥ 0ℚ} → (r *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-non-neg r {r≥0} {p} {q}
  rewrite *-comm r p | *-comm r q = *-monoˡ-≤-non-neg r {r≥0}

*-monoˡ-≤-pos : ∀ r {r>0 : r > 0ℚ} → (_* r) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos r {r>0} = *-monoˡ-≤-non-neg r {<⇒≤ r>0}

*-monoʳ-≤-pos : ∀ r {r>0 : r > 0ℚ} → (r *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos r {r>0} = *-monoʳ-≤-non-neg r {<⇒≤ r>0}

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ r {r>0 : r > 0ℚ} → (_* r) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos r {r>0} {p} {q} p<q = toℚᵘ-cancel-< $ begin-strict
  toℚᵘ (p * r)       ≈⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r <⟨ ℚᵘ.*-monoˡ-<-pos (pos-toℚᵘ r>0) (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r ≈⟨ (ℚᵘ.≃-sym $ toℚᵘ-homo-* q r) ⟩
  toℚᵘ (q * r)       ∎ where open ℚᵘ.≤-Reasoning

*-monoʳ-<-pos : ∀ r {r>0 : r > 0ℚ} → (r *_) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos r {r>0} {p} {q}
  rewrite *-comm r p | *-comm r q = *-monoˡ-<-pos r {r>0}

*-cancelʳ-<-non-neg : ∀ r {r≥0 : r ≥ 0ℚ} {p q} → p * r < q * r → p < q
*-cancelʳ-<-non-neg r {r≥0} {p} {q} p*r<q*r = toℚᵘ-cancel-< $
  ℚᵘ.*-cancelʳ-<-non-neg (non-neg-toℚᵘ r≥0) $ begin-strict
  toℚᵘ p ℚᵘ.* toℚᵘ r ≈⟨ ℚᵘ.≃-sym (toℚᵘ-homo-* p r) ⟩
  toℚᵘ (p * r)       <⟨ toℚᵘ-mono-< p*r<q*r ⟩
  toℚᵘ (q * r)       ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r ∎ where open ℚᵘ.≤-Reasoning

*-cancelˡ-<-non-neg : ∀ r {r≥0 : r ≥ 0ℚ} {p q} → p * r < q * r → p < q
*-cancelˡ-<-non-neg r {r≥0} {p} {q}
  rewrite *-comm r p | *-comm r q = *-cancelʳ-<-non-neg r {r≥0}

------------------------------------------------------------------------
-- Structures

*-isMagma : IsMagma _*_
*-isMagma = *-Monomorphism.*-isMagma ℚᵘ.*-isMagma

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = *-Monomorphism.*-isSemigroup ℚᵘ.*-isSemigroup

*-1-isMonoid : IsMonoid _*_ 1ℚ
*-1-isMonoid = *-Monomorphism.*-isMonoid ℚᵘ.*-1-isMonoid

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℚ
*-1-isCommutativeMonoid = *-Monomorphism.*-isCommutativeMonoid ℚᵘ.*-1-isCommutativeMonoid

+-*-isRing : IsRing _+_ _*_ -_ 0ℚ 1ℚ
+-*-isRing = *-Monomorphism.isRing ℚᵘ.+-*-isRing

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℚ 1ℚ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

------------------------------------------------------------------------
-- Packages

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

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

≤-irrelevance = ≤-irrelevant
{-# WARNING_ON_USAGE ≤-irrelevance
"Warning: ≤-irrelevance was deprecated in v1.0.
Please use ≤-irrelevant instead."
#-}

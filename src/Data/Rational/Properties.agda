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
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base
open import Data.Rational.Unnormalised as ℚᵘ
  using (ℚᵘ; *≡*; *≤*) renaming (↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_; _≃_ to _≃ᵘ_; _≤_ to _≤ᵘ_)
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
-- toℚᵘ is a isomorphism

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

------------------------------------------------------------------------
-- Relational properties

private
  module ≤-Monomorphism = OrderMonomorphisms toℚᵘ-isOrderMonomorphism-≤

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = *≤* ℤ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans = ≤-Monomorphism.trans ℚᵘ.≤-trans

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (ℤ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q = [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′ (ℤ.≤-total (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p))

infix 4 _≤?_
_≤?_ : Decidable _≤_
p ≤? q = Dec.map′ *≤* drop-*≤* (↥ p ℤ.* ↧ q ℤ.≤? ↥ q ℤ.* ↧ p)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant (*≤* p≤q₁) (*≤* p≤q₂) = cong *≤* (ℤ.≤-irrelevant p≤q₁ p≤q₂)

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
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

------------------------------------------------------------------------
-- Bundles

≤-decTotalOrder : DecTotalOrder _ _ _
≤-decTotalOrder = record
  { Carrier         = ℚ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

drop-*<* : ∀ {p q} → p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
drop-*<* (*<* pq<qp) = pq<qp

------------------------------------------------------------------------
-- Relational properties

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (*<* p<p) = ℤ.<-irrefl refl p<p

<-asym : Asymmetric _<_
<-asym (*<* p<q) (*<* q<p) = ℤ.<-asym p<q q<p

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r) = *<*
  (ℤ.*-cancelʳ-<-non-neg _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  ℤ.* sd₃) ℤ.* sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁   ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm sd₃ sd₂) ⟩
  n₁   ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  ℤ.* sd₂) ℤ.* sd₃  <⟨ ℤ.*-monoʳ-<-pos (ℕ.pred (↧ₙ r)) p<q ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) ≤⟨ ℤ.*-monoˡ-≤-pos (ℕ.pred (↧ₙ p)) q≤r ⟩
  sd₁  ℤ.* (n₃  ℤ.* sd₂) ≡⟨ sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃)  ℤ.* sd₂  ≡⟨ cong (ℤ._* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃  ℤ.* sd₁) ℤ.* sd₂  ∎))
  where open ℤ.≤-Reasoning

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {p} {q} {r} (*≤* p≤q) (*<* q<r) = *<*
  (ℤ.*-cancelʳ-<-non-neg _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  ℤ.* sd₃) ℤ.* sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁   ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm sd₃ sd₂) ⟩
  n₁   ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  ℤ.* sd₂) ℤ.* sd₃  ≤⟨ ℤ.*-monoʳ-≤-pos (ℕ.pred (↧ₙ r)) p≤q ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) <⟨ ℤ.*-monoˡ-<-pos (ℕ.pred (↧ₙ p)) q<r ⟩
  sd₁  ℤ.* (n₃  ℤ.* sd₂) ≡⟨ sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃)  ℤ.* sd₂  ≡⟨ cong (ℤ._* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃  ℤ.* sd₁) ℤ.* sd₂  ∎))
  where open ℤ.≤-Reasoning

<-trans : Transitive _<_
<-trans p<q = ≤-<-trans (<⇒≤ p<q)

infix 4 _<?_

_<?_ : Decidable _<_
p <? q = Dec.map′ *<* drop-*<* ((↥ p ℤ.* ↧ q) ℤ.<? (↥ q ℤ.* ↧ p))

<-cmp : Trichotomous _≡_ _<_
<-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ ≡⇒≃) (≯ ∘ drop-*<*)
... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ ≡)   (≯ ∘ drop-*<*)
... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ ≡⇒≃) (*<* >)

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
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp-≡
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

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

------------------------------------------------------------------------
-- Algebraic properties

private
  module +-Monomorphism = GroupMonomorphisms toℚᵘ-isGroupMonomorphism-+

+-assoc : Associative _+_
+-assoc = +-Monomorphism.assoc ℚᵘ.+-isMagma ℚᵘ.+-assoc

+-comm : Commutative _+_
+-comm = +-Monomorphism.comm ℚᵘ.+-isMagma ℚᵘ.+-comm

+-identityˡ : LeftIdentity 0ℚ _+_
+-identityˡ = +-Monomorphism.identityˡ ℚᵘ.+-isMagma ℚᵘ.+-identityˡ

+-identityʳ : RightIdentity 0ℚ _+_
+-identityʳ = +-Monomorphism.identityʳ ℚᵘ.+-isMagma ℚᵘ.+-identityʳ

+-identity : Identity 0ℚ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseˡ : LeftInverse 0ℚ -_ _+_
+-inverseˡ = +-Monomorphism.inverseˡ ℚᵘ.+-isMagma ℚᵘ.+-inverseˡ

+-inverseʳ : RightInverse 0ℚ -_ _+_
+-inverseʳ = +-Monomorphism.inverseʳ ℚᵘ.+-isMagma ℚᵘ.+-inverseʳ

+-inverse : Inverse 0ℚ -_ _+_
+-inverse = +-Monomorphism.inverse ℚᵘ.+-isMagma ℚᵘ.+-inverse

-‿cong :  Congruent₁ (-_)
-‿cong = +-Monomorphism.⁻¹-cong ℚᵘ.+-isMagma ℚᵘ.-‿cong

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

*-identityˡ : LeftIdentity 1ℚ _*_
*-identityˡ = *-Monomorphism.*-identityˡ ℚᵘ.*-isMagma ℚᵘ.*-identityˡ

*-identityʳ : RightIdentity 1ℚ _*_
*-identityʳ = *-Monomorphism.*-identityʳ ℚᵘ.*-isMagma ℚᵘ.*-identityʳ

*-identity : Identity 1ℚ _*_
*-identity = *-identityˡ , *-identityʳ

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = *-Monomorphism.distribˡ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribˡ-+

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = *-Monomorphism.distribʳ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribʳ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

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

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
import Algebra.Morphism.MagmaMonomorphism as MagmaMonomorphisms
import Algebra.Morphism.MonoidMonomorphism as MonoidMonomorphisms
import Algebra.Morphism.GroupMonomorphism as GroupMonomorphisms
import Algebra.Morphism.RingMonomorphism as RingMonomorphisms
import Algebra.Morphism.LatticeMonomorphism as LatticeMonomorphisms
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ; _◃_) renaming (∣_∣ to ∣_∣ᶻ)
open import Data.Integer.Coprimality using (coprime-divisor)
import Data.Integer.Properties as ℤ
open import Data.Integer.GCD using (gcd; gcd[i,j]≡0⇒i≡0; gcd[i,j]≡0⇒j≡0)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤ-solver)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Nat.Coprimality as C using (Coprime; coprime?)
open import Data.Nat.Divisibility hiding (/-cong)
import Data.Nat.GCD as ℕ
import Data.Nat.DivMod as ℕ
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; *≡*; *≤*; *<*) renaming (↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_; _≃_ to _≃ᵘ_; _≤_ to _≤ᵘ_; _<_ to _<ᵘ_; _+_ to _+ᵘ_)
import Data.Rational.Unnormalised.Properties as ℚᵘ
open import Data.Sum.Base
open import Data.Unit using (tt)
import Data.Sign as S
open import Function.Base using (_∘_ ; _$_)
open import Function.Definitions using (Injective)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Morphism.Structures
import Relation.Binary.Morphism.OrderMonomorphism as OrderMonomorphisms
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Nullary.Decidable as Dec
  using (True; False; fromWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary.Decidable as Dec using (True; fromWitness; map′)
open import Relation.Nullary.Product using (_×-dec_)

open import Algebra.Definitions {A = ℚ} _≡_
  hiding (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Definitions
  using (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Structures  {A = ℚ} _≡_

private
  infix 4 _≢0
  _≢0 : ℕ → Set
  n ≢0 = False (n ℕ.≟ 0)

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

mkℚ-injective : ∀ {n₁ n₂ d₁ d₂} .{c₁ : Coprime ∣ n₁ ∣ᶻ (suc d₁)}
                                .{c₂ : Coprime ∣ n₂ ∣ᶻ (suc d₂)} →
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
           .{c₁ : Coprime ∣ n₁ ∣ᶻ (suc d₁)}
           .{c₂ : Coprime ∣ n₂ ∣ᶻ (suc d₂)} →
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
    (C.sym (C.recompute c₁)) $
    divides ∣ n₂ ∣ᶻ $ begin
      ∣ n₁ ℤ.* + suc d₂ ∣ᶻ  ≡⟨ cong ∣_∣ᶻ eq ⟩
      ∣ n₂ ℤ.* + suc d₁ ∣ᶻ  ≡⟨ ℤ.abs-*-commute n₂ (+ suc d₁) ⟩
      ∣ n₂ ∣ᶻ ℕ.* suc d₁    ∎

  1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
  1+d₂∣1+d₁ = coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
    (C.sym (C.recompute c₂)) $
    divides ∣ n₁ ∣ᶻ (begin
      ∣ n₂ ℤ.* + suc d₁ ∣ᶻ  ≡⟨ cong ∣_∣ᶻ (sym eq) ⟩
      ∣ n₁ ℤ.* + suc d₂ ∣ᶻ  ≡⟨ ℤ.abs-*-commute n₁ (+ suc d₂) ⟩
      ∣ n₁ ∣ᶻ ℕ.* suc d₂    ∎)

  helper : mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
  helper with ∣-antisym 1+d₁∣1+d₂ 1+d₂∣1+d₁
  ... | refl with ℤ.*-cancelʳ-≡ n₁ n₂ (+ suc d₁) (λ ()) eq
  ...   | refl = refl

------------------------------------------------------------------------
-- Properties of ↥
------------------------------------------------------------------------

↥p≡0⇒p≡0 : ∀ p → ↥ p ≡ + 0 → p ≡ 0ℚ
↥p≡0⇒p≡0 p ↥p≡0 = ≃⇒≡ (begin-equality
  ↥ p ℤ.* ↧ 0ℚ              ≡⟨ cong (ℤ._* ↧ 0ℚ) ↥p≡0 ⟩
  + 0 ℤ.* ↧ 0ℚ              ≡⟨ ℤ.*-zeroˡ (↧ 0ℚ) ⟩
  + 0                       ≡˘⟨ ℤ.*-zeroˡ (↧ p) ⟩
  + 0 ℤ.* ↧ p               ≡⟨⟩
  ↥ 0ℚ ℤ.* ↧ p              ∎)
  where
    open ℤ.≤-Reasoning

p≡0⇒↥p≡0 : ∀ p → p ≡ 0ℚ → ↥ p ≡ + 0
p≡0⇒↥p≡0 p refl = refl

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
  c′ = C.recompute c
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

normalize-cong : ∀ {m₁ n₁ m₂ n₂ n₁≢0 n₂≢0} → m₁ ≡ m₂ → n₁ ≡ n₂ → normalize m₁ n₁ {n₁≢0} ≡ normalize m₂ n₂ {n₂≢0}
normalize-cong {m} {n} {.m} {.n} {n≢0₁} {n≢0₂} refl refl = mkℚ+-cong n/g₁≢0 n/g₂≢0 (ℕ./-congʳ {n = g} {g} refl) (ℕ./-congʳ {n = g} {g} refl)
  where
    g = ℕ.gcd m n
    g₁≢0 = ℕ.gcd[m,n]≢0 m n (inj₂ (toWitnessFalse n≢0₁))
    g₂≢0 = ℕ.gcd[m,n]≢0 m n (inj₂ (toWitnessFalse n≢0₂))
    n/g₁ = (n ℕ./ g) {fromWitnessFalse g₁≢0}
    n/g₂ = (n ℕ./ g) {fromWitnessFalse g₂≢0}
    n/g₁≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 m n {n≢0₁} {fromWitnessFalse g₁≢0})
    n/g₂≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 m n {n≢0₂} {fromWitnessFalse g₂≢0})

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

toℚᵘ-fromℚᵘ : ∀ p → toℚᵘ (fromℚᵘ p) ≃ᵘ p
toℚᵘ-fromℚᵘ (ℚᵘ.mkℚᵘ (+ n) d-1) = *≡* $ begin
  (↥ᵘ toℚᵘ (fromℚᵘ (ℚᵘ.mkℚᵘ (+ n) d-1))) ℤ.* (↧ᵘ ℚᵘ.mkℚᵘ (+ n) d-1) ≡⟨⟩
  (↥ᵘ toℚᵘ (normalize n (suc d-1))) ℤ.* (↧ᵘ ℚᵘ.mkℚᵘ (+ n) d-1) ≡⟨⟩
  (↥ᵘ toℚᵘ (mkℚ+ (n ℕ./ g) (suc d-1 ℕ./ g) {d/g≢0} {!!})) ℤ.* (↧ᵘ ℚᵘ.mkℚᵘ (+ n) d-1) ≡⟨ {!!} ⟩
  + n ℤ.* (↧ᵘ toℚᵘ (fromℚᵘ (ℚᵘ.mkℚᵘ (+ n) d-1))) ∎
  where
    open ≡-Reasoning
    g = ℕ.gcd n (suc d-1)
    g≢0 = fromWitnessFalse (ℕ.gcd[m,n]≢0 n (suc d-1) (inj₂ ℕ.1+n≢0))
    d/g≢0 = fromWitnessFalse (ℕ.n/gcd[m,n]≢0 n (suc d-1) {fromWitnessFalse ℕ.1+n≢0} {g≢0})
    --n/g≢0 = fromWitnessFalse (n/gcd[m,n]≢0 m n {n≢0} {g≢0})
toℚᵘ-fromℚᵘ (ℚᵘ.mkℚᵘ -[1+ n ] d-1) = {!!}

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
-- toℚᵘ is a isomorphism

toℚᵘ-mono-< : ∀ {p q} → p < q → toℚᵘ p <ᵘ toℚᵘ q
toℚᵘ-mono-< (*<* p<q) = *<* p<q

toℚᵘ-cancel-< : ∀ {p q} → toℚᵘ p <ᵘ toℚᵘ q → p < q
toℚᵘ-cancel-< (*<* p<q) = *<* p<q

------------------------------------------------------------------------
-- Relational properties

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {p} {q} p≮q = *≤* (ℤ.≮⇒≥ (p≮q ∘ *<*))

≰⇒> : _≰_ ⇒ _>_
≰⇒> {p} {q} p≰q = *<* (ℤ.≰⇒> (p≰q ∘ *≤*))

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ {p} {q} (*<* p<q) = ℤ.<⇒≢ p<q ∘ ≡⇒≃

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (*<* p<p) = ℤ.<-irrefl refl p<p

<-asym : Asymmetric _<_
<-asym (*<* p<q) (*<* q<p) = ℤ.<-asym p<q q<p

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r) = *<*
  (ℤ.*-cancelʳ-<-nonNeg _ (begin-strict
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
  (ℤ.*-cancelʳ-<-nonNeg _ (begin-strict
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
-- Properties of Positive/NonPositive/Negative/NonNegative and _≤_/_<_

positive⁻¹ : ∀ {q} → Positive q → q > 0ℚ
positive⁻¹ {q} q>0 = toℚᵘ-cancel-< (ℚᵘ.positive⁻¹ q>0)

nonNegative⁻¹ : ∀ {q} → NonNegative q → q ≥ 0ℚ
nonNegative⁻¹ {q} q≥0 = toℚᵘ-cancel-≤ (ℚᵘ.nonNegative⁻¹ q≥0)

negative⁻¹ : ∀ {q} → Negative q → q < 0ℚ
negative⁻¹ {q} q<0 = toℚᵘ-cancel-< (ℚᵘ.negative⁻¹ q<0)

nonPositive⁻¹ : ∀ {q} → NonPositive q → q ≤ 0ℚ
nonPositive⁻¹ {q} q≤0 = toℚᵘ-cancel-≤ (ℚᵘ.nonPositive⁻¹ q≤0)

negative<positive : ∀ {p q} → Negative p → Positive q → p < q
negative<positive p<0 q>0 = toℚᵘ-cancel-< (ℚᵘ.negative<positive p<0 q>0)

------------------------------------------------------------------------
-- Properties of -_ and _≤_/_<_
------------------------------------------------------------------------

neg-mono-<-> : -_ Preserves _<_ ⟶ _>_
neg-mono-<-> {mkℚ (-[1+_] p₁) q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*<* (ℤ.-<- n<m)) = *<* (ℤ.+<+ (ℕ.s≤s n<m))
neg-mono-<-> {mkℚ (-[1+_] p₁) q₁ _} {mkℚ +0 q₂ _} (*<* ℤ.-<+) = *<* (ℤ.+<+ (ℕ.s≤s ℕ.z≤n))
neg-mono-<-> {mkℚ (-[1+_] p₁) q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*<* ℤ.-<+) = *<* ℤ.-<+
neg-mono-<-> {mkℚ +0 q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*<* ())
neg-mono-<-> {mkℚ +0 q₁ _} {mkℚ +0 q₂ _} (*<* (ℤ.+<+ m<n)) = *<* (ℤ.+<+ m<n)
neg-mono-<-> {mkℚ +0 q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*<* (ℤ.+<+ m<n)) = *<* ℤ.-<+
neg-mono-<-> {mkℚ +[1+ p₁ ] q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*<* ())
neg-mono-<-> {mkℚ +[1+ p₁ ] q₁ _} {mkℚ +0 q₂ _} (*<* (ℤ.+<+ ()))
neg-mono-<-> {mkℚ +[1+ p₁ ] q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*<* (ℤ.+<+ (ℕ.s≤s m<n))) = *<* (ℤ.-<- m<n)

neg-mono-≤-≥ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤-≥ {mkℚ (-[1+_] p₁) q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*≤* (ℤ.-≤- n≤m)) = *≤* (ℤ.+≤+ (ℕ.s≤s n≤m))
neg-mono-≤-≥ {mkℚ (-[1+_] p₁) q₁ _} {mkℚ +0 q₂ _} (*≤* ℤ.-≤+) = *≤* (ℤ.+≤+ ℕ.z≤n)
neg-mono-≤-≥ {mkℚ (-[1+_] p₁) q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*≤* ℤ.-≤+) = *≤* ℤ.-≤+
neg-mono-≤-≥ {mkℚ +0 q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*≤* ())
neg-mono-≤-≥ {mkℚ +0 q₁ _} {mkℚ +0 q₂ _} (*≤* (ℤ.+≤+ m≤n)) = *≤* (ℤ.+≤+ m≤n)
neg-mono-≤-≥ {mkℚ +0 q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*≤* (ℤ.+≤+ m≤n)) = *≤* ℤ.-≤+
neg-mono-≤-≥ {mkℚ +[1+ p₁ ] q₁ _} {mkℚ (-[1+_] p₂) q₂ _} (*≤* ())
neg-mono-≤-≥ {mkℚ +[1+ p₁ ] q₁ _} {mkℚ +0 q₂ _} (*≤* (ℤ.+≤+ ()))
neg-mono-≤-≥ {mkℚ +[1+ p₁ ] q₁ _} {mkℚ +[1+ p₂ ] q₂ _} (*≤* (ℤ.+≤+ (ℕ.s≤s m≤n))) = *≤* (ℤ.-≤- m≤n)

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

/-cong : ∀ {p₁ q₁ p₂ q₂ q₁≢0 q₂≢0} → p₁ ≡ p₂ → q₁ ≡ q₂ → (p₁ / q₁) {q₁≢0} ≡ (p₂ / q₂) {q₂≢0}
/-cong {+_ n} {q} {.(+ n)} {.q} {q≢0₁} {q≢0₂} refl refl = normalize-cong {n} {q} {n} {q} {q≢0₁} {q≢0₂} refl refl
/-cong { -[1+_] n} {q} {.(-[1+ n ])} {.q} {q≢0₁} {q≢0₂} refl refl = cong -_ (normalize-cong {suc n} {q} {suc n} {q} {q≢0₁} {q≢0₂} refl refl)

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
-- Properties of _+_ and _≤_/_<_

+-monoʳ-< : ∀ x → (λ h → x + h) Preserves _<_ ⟶ _<_
+-monoʳ-< x {y} {z} y<z = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (x + y)                                    ≈⟨ toℚᵘ-homo-+ x y ⟩
  toℚᵘ x +ᵘ toℚᵘ y                                <⟨ ℚᵘ.+-monoʳ-< (toℚᵘ x) (toℚᵘ-mono-< y<z) ⟩
  toℚᵘ x +ᵘ toℚᵘ z                                ≈˘⟨ toℚᵘ-homo-+ x z ⟩
  toℚᵘ (x + z)                                    ∎)
  where
    open ℚᵘ.≤-Reasoning

+-monoˡ-< : ∀ x → (λ h → h + x) Preserves _<_ ⟶ _<_
+-monoˡ-< x {y} {z} y<z = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (y + x)                                    ≈⟨ toℚᵘ-homo-+ y x ⟩
  toℚᵘ y +ᵘ toℚᵘ x                                <⟨ ℚᵘ.+-monoˡ-< (toℚᵘ x) (toℚᵘ-mono-< y<z) ⟩
  toℚᵘ z +ᵘ toℚᵘ x                                ≈˘⟨ toℚᵘ-homo-+ z x ⟩
  toℚᵘ (z + x)                                    ∎)
  where
    open ℚᵘ.≤-Reasoning

+-monoʳ-≤ : ∀ x → (λ h → x + h) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x {y} {z} y≤z = toℚᵘ-cancel-≤ (begin
  toℚᵘ (x + y)                                    ≈⟨ toℚᵘ-homo-+ x y ⟩
  toℚᵘ x +ᵘ toℚᵘ y                                ≤⟨ ℚᵘ.+-monoʳ-≤ (toℚᵘ x) (toℚᵘ-mono-≤ y≤z) ⟩
  toℚᵘ x +ᵘ toℚᵘ z                                ≈˘⟨ toℚᵘ-homo-+ x z ⟩
  toℚᵘ (x + z)                                    ∎)
  where
    open ℚᵘ.≤-Reasoning

+-monoˡ-≤ : ∀ x → (λ h → h + x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x {y} {z} y≤z = toℚᵘ-cancel-≤ (begin
  toℚᵘ (y + x)                                    ≈⟨ toℚᵘ-homo-+ y x ⟩
  toℚᵘ y +ᵘ toℚᵘ x                                ≤⟨ ℚᵘ.+-monoˡ-≤ (toℚᵘ x) (toℚᵘ-mono-≤ y≤z) ⟩
  toℚᵘ z +ᵘ toℚᵘ x                                ≈˘⟨ toℚᵘ-homo-+ z x ⟩
  toℚᵘ (z + x)                                    ∎)
  where
    open ℚᵘ.≤-Reasoning

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {y} {u} {v} x≤y u≤v = ≤-trans (+-monoˡ-≤ u x≤y) (+-monoʳ-≤ y u≤v)

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {x} {y} {u} {v} x<y u<v = <-trans (+-monoˡ-< u x<y) (+-monoʳ-< y u<v)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {x} {y} {u} {v} x≤y u<v = ≤-<-trans (+-monoˡ-≤ u x≤y) (+-monoʳ-< y u<v)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {x} {y} {u} {v} x<y u≤v = <-≤-trans (+-monoˡ-< u x<y) (+-monoʳ-≤ y u≤v)

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

toℚᵘ-homo-1/ : ∀ p {p≢0} → toℚᵘ ((1/ p) {p≢0}) ℚᵘ.≃ (ℚᵘ.1/ toℚᵘ p) {p≢0}
toℚᵘ-homo-1/ (mkℚ +[1+ _ ] _ _) = ℚᵘ.≃-refl
toℚᵘ-homo-1/ (mkℚ -[1+ _ ] _ _) = ℚᵘ.≃-refl

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

*-inverseˡ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → ((1/ p) {p≢0}) * p ≡ 1ℚ
*-inverseˡ p {p≢0} = toℚᵘ-injective (begin-equality
  toℚᵘ ((1/ p) * p)                ≈⟨ toℚᵘ-homo-* (1/ p) p ⟩
  toℚᵘ ((1/ p) {p≢0}) ℚᵘ.* toℚᵘ p  ≈⟨ ℚᵘ.*-congʳ (toℚᵘ p) (toℚᵘ-homo-1/ p {p≢0}) ⟩
  (ℚᵘ.1/ toℚᵘ p) {p≢0} ℚᵘ.* toℚᵘ p ≈⟨ ℚᵘ.*-inverseˡ (toℚᵘ p) {p≢0} ⟩
  ℚᵘ.1ℚᵘ ∎)
  where
    open ℚᵘ.≤-Reasoning

*-inverseʳ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → p * ((1/ p) {p≢0}) ≡ 1ℚ
*-inverseʳ p {p≢0} = begin
  p * (1/ p)                       ≡⟨ *-comm p (1/ p) ⟩
  (1/ p) {p≢0} * p                 ≡⟨ *-inverseˡ p {p≢0} ⟩
  1ℚ                               ∎
  where
    open ≡-Reasoning

*-zeroˡ : LeftZero 0ℚ _*_
*-zeroˡ = *-Monomorphism.zeroˡ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-zeroˡ

*-zeroʳ : RightZero 0ℚ _*_
*-zeroʳ = *-Monomorphism.zeroʳ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-zeroʳ

*-zero : Zero 0ℚ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = *-Monomorphism.distribˡ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribˡ-+

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = *-Monomorphism.distribʳ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribʳ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-inverseˡ : ∀ p {p≢0 : ∣ ↥ p ∣ ≢0} → (1/ p) {p≢0} * p ≡ 1ℚ
*-inverseˡ p {p≢0} = toℚᵘ-injective (begin-equality
  toℚᵘ (1/ p * p)             ≈⟨ toℚᵘ-homo-* (1/ p) p ⟩
  toℚᵘ (1/ p) ℚᵘ.* toℚᵘ p     ≈⟨ ℚᵘ.*-congʳ (toℚᵘ-homo-1/ p {p≢0}) ⟩
  ℚᵘ.1/ (toℚᵘ p) ℚᵘ.* toℚᵘ p  ≈⟨ ℚᵘ.*-inverseˡ (toℚᵘ p) {p≢0} ⟩
  ℚᵘ.1ℚᵘ                      ∎
  )
  where open ℚᵘ.≤-Reasoning

*-inverseʳ : ∀ p {p≢0 : ∣ ↥ p ∣ ≢0} → p * (1/ p) {p≢0} ≡ 1ℚ
*-inverseʳ p {p≢0} = trans (*-comm p (1/ p)) (*-inverseˡ p {p≢0})

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-cancelʳ-≤-pos : ∀ {r} → Positive r → ∀ {p q} → p * r ≤ q * r → p ≤ q
*-cancelʳ-≤-pos {r} r>0 {p} {q} pr≤qr = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelʳ-≤-pos {toℚᵘ r} r>0 (begin
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             ≤⟨ toℚᵘ-mono-≤ pr≤qr ⟩
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-≤-pos : ∀ {r} → Positive r → ∀ {p q} → r * p ≤ r * q → p ≤ q
*-cancelˡ-≤-pos {r} r>0 {p} {q} rp≤rq = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelˡ-≤-pos {toℚᵘ r} r>0 (begin
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             ≤⟨ toℚᵘ-mono-≤ rp≤rq ⟩
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-monoʳ-≤-nonNeg : ∀ {r} → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-nonNeg {r} r≥0 {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (p * r)                             ≈⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≤⟨ ℚᵘ.*-monoˡ-≤-nonNeg r≥0 (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ (q * r)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoˡ-≤-nonNeg : ∀ {r} → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-nonNeg {r} r≥0 {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (r * p)                             ≈⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≤⟨ ℚᵘ.*-monoʳ-≤-nonNeg {toℚᵘ r} r≥0 (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ≈˘⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ (r * q)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoʳ-≤-pos : ∀ {r} → Positive r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos {r} = *-monoʳ-≤-nonNeg {r} ∘ ℚᵘ.positive⇒nonNegative {toℚᵘ r}

*-monoˡ-≤-pos : ∀ {r} → Positive r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos {r} = *-monoˡ-≤-nonNeg {r} ∘ ℚᵘ.positive⇒nonNegative {toℚᵘ r}

*-monoʳ-≤-nonPos-≥ : ∀ {r} → NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-nonPos-≥ {r} r≤0 {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ≤⟨ ℚᵘ.*-monoˡ-≤-nonPos-≥ {toℚᵘ r} r≤0 (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoˡ-≤-nonPos-≥ : ∀ {r} → NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-nonPos-≥ {r} r≤0 {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ≤⟨ ℚᵘ.*-monoʳ-≤-nonPos-≥ {toℚᵘ r} r≤0 (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoʳ-≤-neg : ∀ {r} → Negative r → (_* r) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-neg {r} = *-monoʳ-≤-nonPos-≥ {r} ∘ ℚᵘ.negative⇒nonPositive {toℚᵘ r}

*-monoˡ-≤-neg : ∀ {r} → Negative r → (r *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-neg {r} = *-monoˡ-≤-nonPos-≥ {r} ∘ ℚᵘ.negative⇒nonPositive {toℚᵘ r}

*-cancelʳ-≤-neg-≥ : ∀ {r} → Negative r → ∀ {p q} → p * r ≤ q * r → p ≥ q
*-cancelʳ-≤-neg-≥ {r} r≤0 {p} {q} pr≤qr = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelʳ-≤-neg-≥ r≤0 (begin
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             ≤⟨ toℚᵘ-mono-≤ pr≤qr ⟩
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-≤-neg-≥ : ∀ {r} → Negative r → ∀ {p q} → r * p ≤ r * q → p ≥ q
*-cancelˡ-≤-neg-≥ {r} r≤0 {p} {q} rp≤rq = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelˡ-≤-neg-≥ {toℚᵘ r} r≤0 (begin
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             ≤⟨ toℚᵘ-mono-≤ rp≤rq ⟩
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ∎))
  where
    open ℚᵘ.≤-Reasoning

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-monoˡ-<-pos : ∀ {r} (r>0 : Positive r) → (_* r) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos {r} r>0 {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (p * r)                             ≈⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r                       <⟨ ℚᵘ.*-monoˡ-<-pos {toℚᵘ r} r>0 (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ (q * r)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoʳ-<-pos : ∀ {r} (r>0 : Positive r) → (r *_) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos {r} r>0 {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (r * p)                             ≈⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ p                       <⟨ ℚᵘ.*-monoʳ-<-pos {toℚᵘ r} r>0 (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ≈˘⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ (r * q)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-<-nonNeg : ∀ {r} (r≥0 : NonNegative r) {p q} → r * p < r * q → p < q
*-cancelˡ-<-nonNeg {r} r≥0 {p} {q} rp<rq = toℚᵘ-cancel-< (ℚᵘ.*-cancelˡ-<-nonNeg {toℚᵘ r} r≥0 (begin-strict
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             <⟨ toℚᵘ-mono-< rp<rq ⟩
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelʳ-<-nonNeg : ∀ {r} (r≥0 : NonNegative r) {p q} → p * r < q * r → p < q
*-cancelʳ-<-nonNeg {r} r≥0 {p} {q} pr<qr = toℚᵘ-cancel-< (ℚᵘ.*-cancelʳ-<-nonNeg {toℚᵘ r} r≥0 (begin-strict
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             <⟨ toℚᵘ-mono-< pr<qr ⟩
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-<-pos : ∀ {r} (r>0 : Positive r) {p q} → r * p < r * q → p < q
*-cancelˡ-<-pos {r} = *-cancelˡ-<-nonNeg {r} ∘ ℚᵘ.positive⇒nonNegative {toℚᵘ r}

*-cancelʳ-<-pos : ∀ {r} (r>0 : Positive r) {p q} → p * r < q * r → p < q
*-cancelʳ-<-pos {r} = *-cancelʳ-<-nonNeg {r} ∘ ℚᵘ.positive⇒nonNegative {toℚᵘ r}

*-monoˡ-<-neg-> : ∀ {r} (r<0 : Negative r) → (_* r) Preserves _<_ ⟶ _>_
*-monoˡ-<-neg-> {r} r<0 {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       <⟨ ℚᵘ.*-monoˡ-<-neg-> {toℚᵘ r} r<0 (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-monoʳ-<-neg-> : ∀ {r} (r<0 : Negative r) → (r *_) Preserves _<_ ⟶ _>_
*-monoʳ-<-neg-> {r} r<0 {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       <⟨ ℚᵘ.*-monoʳ-<-neg-> {toℚᵘ r} r<0 (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             ∎)
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-<-nonPos-> : ∀ {r} (r≤0 : NonPositive r) {p q} → r * p < r * q → p > q
*-cancelˡ-<-nonPos-> {r} r≤0 {p} {q} rp<rq = toℚᵘ-cancel-< (ℚᵘ.*-cancelˡ-<-nonPos-> {toℚᵘ r} r≤0 (begin-strict
  toℚᵘ r ℚᵘ.* toℚᵘ p                       ≈˘⟨ toℚᵘ-homo-* r p ⟩
  toℚᵘ (r * p)                             <⟨ toℚᵘ-mono-< rp<rq ⟩
  toℚᵘ (r * q)                             ≈⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelʳ-<-nonPos-> : ∀ {r} (r≤0 : NonPositive r) {p q} → p * r < q * r → p > q
*-cancelʳ-<-nonPos-> {r} r≤0 {p} {q} pr<qr = toℚᵘ-cancel-< (ℚᵘ.*-cancelʳ-<-nonPos-> {toℚᵘ r} r≤0 (begin-strict
  toℚᵘ p ℚᵘ.* toℚᵘ r                       ≈˘⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ (p * r)                             <⟨ toℚᵘ-mono-< pr<qr ⟩
  toℚᵘ (q * r)                             ≈⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r                       ∎))
  where
    open ℚᵘ.≤-Reasoning

*-cancelˡ-<-neg-> : ∀ {r} (r<0 : Negative r) {p q} → r * p < r * q → p > q
*-cancelˡ-<-neg-> {r} = *-cancelˡ-<-nonPos-> {r} ∘ ℚᵘ.negative⇒nonPositive {toℚᵘ r}

*-cancelʳ-<-neg-> : ∀ {r} (r<0 : Negative r) {p q} → p * r < q * r → p > q
*-cancelʳ-<-neg-> {r} = *-cancelʳ-<-nonPos-> {r} ∘ ℚᵘ.negative⇒nonPositive {toℚᵘ r}

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
+-*-isCommutativeRing = *-Monomorphism.isCommutativeRing ℚᵘ.+-*-isCommutativeRing

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
-- Properties of _⊓_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Monomorphic to unnormalised _⊓_

toℚᵘ-homo-⊓ : Homomorphic₂ toℚᵘ _⊓_ ℚᵘ._⊓_
toℚᵘ-homo-⊓ p q = *≡* $ ℤ.*-cancelʳ-≡ lhs rhs mul mul≢0 $ begin
  lhs ℤ.* mul                                               ≡⟨⟩
  (↥ (p ⊓ q) ℤ.* + ↧p↧q) ℤ.* mul                            ≡⟨ solve 3 (λ a b c → ((a :* b) :* c) := ((a :* c) :* b)) refl (↥ (p ⊓ q)) (+ ↧p↧q) mul ⟩
  (↥ ((↥p↧q ℤ.⊓ ↥q↧p) / ↧p↧q) ℤ.* mul) ℤ.* + ↧p↧q           ≡⟨ cong (ℤ._* + ↧p↧q) (↥-/ (↥p↧q ℤ.⊓ ↥q↧p) ↧p↧q) ⟩
  (↥p↧q ℤ.⊓ ↥q↧p) ℤ.* + ↧p↧q                                ≡˘⟨ cong ((↥p↧q ℤ.⊓ ↥q↧p) ℤ.*_) (↧-/ (↥p↧q ℤ.⊓ ↥q↧p) ↧p↧q) ⟩
  (↥p↧q ℤ.⊓ ↥q↧p) ℤ.* (↧ (p ⊓ q) ℤ.* mul)                   ≡˘⟨ ℤ.*-assoc (↥p↧q ℤ.⊓ ↥q↧p) (↧ (p ⊓ q)) mul ⟩
  rhs ℤ.* mul                                               ∎
  where
    open ≡-Reasoning
    open ℤ-solver
    lhs = ↥ (p ⊓ q) ℤ.* ↧ᵘ (toℚᵘ p ℚᵘ.⊓ toℚᵘ q)
    rhs = ↥ᵘ (toℚᵘ p ℚᵘ.⊓ toℚᵘ q) ℤ.* ↧ (p ⊓ q)
    ↥p↧q = ↥ p ℤ.* ↧ q
    ↥q↧p = ↥ q ℤ.* ↧ p
    ↧p↧q = ↧ₙ p ℕ.* ↧ₙ q
    mul = gcd (↥p↧q ℤ.⊓ ↥q↧p) (+ ↧p↧q)
    mul≢0 : mul ≢ + 0
    mul≢0 = contraposition (gcd[i,j]≡0⇒j≡0 {↥p↧q ℤ.⊓ ↥q↧p} {+ ↧p↧q}) (ℕ.1+n≢0 ∘ ℤ.+-injective)

⊓-rawMagma : RawMagma _ _
⊓-rawMagma = record
  { Carrier = ℚ
  ; _≈_ = _≡_
  ; _∙_ = _⊓_
  }

toℚᵘ-isMagmaHomomorphism-⊓ : IsMagmaHomomorphism ⊓-rawMagma ℚᵘ.⊓-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-⊓ = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; homo = toℚᵘ-homo-⊓
  }

toℚᵘ-isMagmaMonomorphism-⊓ : IsMagmaMonomorphism ⊓-rawMagma ℚᵘ.⊓-rawMagma toℚᵘ
toℚᵘ-isMagmaMonomorphism-⊓ = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-⊓
  ; injective = toℚᵘ-injective
  }

private
  module ⊓-Monomorphism = MagmaMonomorphisms toℚᵘ-isMagmaMonomorphism-⊓

------------------------------------------------------------------------
-- Algebraic properties

⊓-comm : Commutative _⊓_
⊓-comm = ⊓-Monomorphism.comm ℚᵘ.⊓-isMagma ℚᵘ.⊓-comm

⊓-assoc : Associative _⊓_
⊓-assoc = ⊓-Monomorphism.assoc ℚᵘ.⊓-isMagma ℚᵘ.⊓-assoc

⊓-idem : Idempotent _⊓_
⊓-idem = ⊓-Monomorphism.idem ℚᵘ.⊓-isMagma ℚᵘ.⊓-idem

⊓-sel : Selective _⊓_
⊓-sel = ⊓-Monomorphism.sel ℚᵘ.⊓-isMagma ℚᵘ.⊓-sel

------------------------------------------------------------------------
-- Other properties

p≤q⇒p⊓q≡p : ∀ {p q} → p ≤ q → p ⊓ q ≡ p
p≤q⇒p⊓q≡p {p} {q} p≤q = toℚᵘ-injective $ begin-equality
  toℚᵘ (p ⊓ q)                  ≈⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q            ≈⟨ ℚᵘ.p≤q⇒p⊓q≃p (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ p                        ∎
  where
    open ℚᵘ.≤-Reasoning

p⊓q≡p⇒p≤q : ∀ {p q} → p ⊓ q ≡ p → p ≤ q
p⊓q≡p⇒p≤q {p} {q} p⊓q≡p = toℚᵘ-cancel-≤ (ℚᵘ.p⊓q≃p⇒p≤q (begin-equality
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q ≈˘⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ (p ⊓ q)       ≡⟨ cong toℚᵘ p⊓q≡p ⟩
  toℚᵘ p             ∎))
  where
    open ℚᵘ.≤-Reasoning

q≤p⇒p⊓q≡q : ∀ {p q} → q ≤ p → p ⊓ q ≡ q
q≤p⇒p⊓q≡q {p} {q} q≤p = toℚᵘ-injective $ begin-equality
  toℚᵘ (p ⊓ q)                  ≈⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q            ≈⟨ ℚᵘ.q≤p⇒p⊓q≃q (toℚᵘ-mono-≤ q≤p) ⟩
  toℚᵘ q                        ∎
  where
    open ℚᵘ.≤-Reasoning

p⊓q≡p⇒q≤p : ∀ {p q} → p ⊓ q ≡ q → q ≤ p
p⊓q≡p⇒q≤p {p} {q} p⊓q≡q = toℚᵘ-cancel-≤ (ℚᵘ.p⊓q≃q⇒q≤p (begin-equality
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q            ≈˘⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ (p ⊓ q)                  ≡⟨ cong toℚᵘ p⊓q≡q ⟩
  toℚᵘ q                        ∎))
  where
    open ℚᵘ.≤-Reasoning

p⊓q≤p : ∀ p q → p ⊓ q ≤ p
p⊓q≤p p q = toℚᵘ-cancel-≤ $ begin
  toℚᵘ (p ⊓ q)                  ≈⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q            ≤⟨ ℚᵘ.p⊓q≤p (toℚᵘ p) (toℚᵘ q) ⟩
  toℚᵘ p                        ∎
  where
    open ℚᵘ.≤-Reasoning

p⊓q≤q : ∀ p q → p ⊓ q ≤ q
p⊓q≤q p q = toℚᵘ-cancel-≤ $ begin
  toℚᵘ (p ⊓ q)                  ≈⟨ toℚᵘ-homo-⊓ p q ⟩
  toℚᵘ p ℚᵘ.⊓ toℚᵘ q            ≤⟨ ℚᵘ.p⊓q≤q (toℚᵘ p) (toℚᵘ q) ⟩
  toℚᵘ q                        ∎
  where
    open ℚᵘ.≤-Reasoning

mono-≤-distrib-⊓ : ∀ f → f Preserves _≤_ ⟶ _≤_ → ∀ p q → f (p ⊓ q) ≡ f p ⊓ f q
mono-≤-distrib-⊓ f f-mono-≤ p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊓ q)                     ≡⟨ cong f (p≤q⇒p⊓q≡p (<⇒≤ p<q)) ⟩
  f p                           ≡˘⟨ p≤q⇒p⊓q≡p (f-mono-≤ (<⇒≤ p<q)) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊓ q)                     ≡⟨ cong f (⊓-idem p) ⟩
  f p                           ≡˘⟨ ⊓-idem (f p) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊓ q)                     ≡⟨ cong f (q≤p⇒p⊓q≡q (<⇒≤ p>q)) ⟩
  f q                           ≡˘⟨ q≤p⇒p⊓q≡q (f-mono-≤ (<⇒≤ p>q)) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning

mono-<-distrib-⊓ : ∀ f → f Preserves _<_ ⟶ _<_ → ∀ p q → f (p ⊓ q) ≡ f p ⊓ f q
mono-<-distrib-⊓ f f-mono-< p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊓ q)                     ≡⟨ cong f (p≤q⇒p⊓q≡p (<⇒≤ p<q)) ⟩
  f p                           ≡˘⟨ p≤q⇒p⊓q≡p (<⇒≤ (f-mono-< p<q)) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊓ q)                     ≡⟨ cong f (⊓-idem p) ⟩
  f p                           ≡˘⟨ ⊓-idem (f p) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊓ q)                     ≡⟨ cong f (q≤p⇒p⊓q≡q (<⇒≤ p>q)) ⟩
  f q                           ≡˘⟨ q≤p⇒p⊓q≡q (<⇒≤ (f-mono-< p>q)) ⟩
  f p ⊓ f q                     ∎
  where
    open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _⊓_ and _*_

*-distribˡ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊓ (p * r)
*-distribˡ-⊓-nonNeg p p≥0 q r = mono-≤-distrib-⊓ (p *_) (*-monoˡ-≤-nonNeg {p} p≥0) q r

*-distribʳ-⊓-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊓ (r * p)
*-distribʳ-⊓-nonNeg p p≥0 q r = mono-≤-distrib-⊓ (_* p) (*-monoʳ-≤-nonNeg {p} p≥0) q r

------------------------------------------------------------------------
-- Structures

⊓-isMagma : IsMagma _⊓_
⊓-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = cong₂ _⊓_
  }

⊓-isSemigroup : IsSemigroup _⊓_
⊓-isSemigroup = record
  { isMagma = ⊓-isMagma
  ; assoc = ⊓-assoc
  }

⊓-isBand : IsBand _⊓_
⊓-isBand = record
  { isSemigroup = ⊓-isSemigroup
  ; idem = ⊓-idem
  }

⊓-isCommutativeSemigroup : IsCommutativeSemigroup _⊓_
⊓-isCommutativeSemigroup = record
  { isSemigroup = ⊓-isSemigroup
  ; comm = ⊓-comm
  }

⊓-isSemilattice : IsSemilattice _⊓_
⊓-isSemilattice = record
  { isBand = ⊓-isBand
  ; comm = ⊓-comm
  }

⊓-isSelectiveMagma : IsSelectiveMagma _⊓_
⊓-isSelectiveMagma = record
  { isMagma = ⊓-isMagma
  ; sel = ⊓-sel
  }

------------------------------------------------------------------------
-- Bundles

⊓-magma : Magma _ _
⊓-magma = record
  { isMagma = ⊓-isMagma
  }

⊓-semigroup : Semigroup _ _
⊓-semigroup = record
  { isSemigroup = ⊓-isSemigroup
  }

⊓-band : Band _ _
⊓-band = record
  { isBand = ⊓-isBand
  }

⊓-commutativeSemigroup : CommutativeSemigroup _ _
⊓-commutativeSemigroup = record
  { isCommutativeSemigroup = ⊓-isCommutativeSemigroup
  }

⊓-semilattice : Semilattice _ _
⊓-semilattice = record
  { isSemilattice = ⊓-isSemilattice
  }

⊓-selectiveMagma : SelectiveMagma _ _
⊓-selectiveMagma = record
  { isSelectiveMagma = ⊓-isSelectiveMagma
  }

------------------------------------------------------------------------
-- Properties of _⊔_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Monomorphic to unnormalised _⊔_

toℚᵘ-homo-⊔ : Homomorphic₂ toℚᵘ _⊔_ ℚᵘ._⊔_
toℚᵘ-homo-⊔ p q = *≡* $ ℤ.*-cancelʳ-≡ lhs rhs mul mul≢0 $ begin
  lhs ℤ.* mul                                               ≡⟨⟩
  (↥ (p ⊔ q) ℤ.* + ↧p↧q) ℤ.* mul                            ≡⟨ solve 3 (λ a b c → ((a :* b) :* c) := ((a :* c) :* b)) refl (↥ (p ⊔ q)) (+ ↧p↧q) mul ⟩
  (↥ ((↥p↧q ℤ.⊔ ↥q↧p) / ↧p↧q) ℤ.* mul) ℤ.* + ↧p↧q           ≡⟨ cong (ℤ._* + ↧p↧q) (↥-/ (↥p↧q ℤ.⊔ ↥q↧p) ↧p↧q) ⟩
  (↥p↧q ℤ.⊔ ↥q↧p) ℤ.* + ↧p↧q                                ≡˘⟨ cong ((↥p↧q ℤ.⊔ ↥q↧p) ℤ.*_) (↧-/ (↥p↧q ℤ.⊔ ↥q↧p) ↧p↧q) ⟩
  (↥p↧q ℤ.⊔ ↥q↧p) ℤ.* (↧ (p ⊔ q) ℤ.* mul)                   ≡˘⟨ ℤ.*-assoc (↥p↧q ℤ.⊔ ↥q↧p) (↧ (p ⊔ q)) mul ⟩
  rhs ℤ.* mul                                               ∎
  where
    open ≡-Reasoning
    open ℤ-solver
    lhs = ↥ (p ⊔ q) ℤ.* ↧ᵘ (toℚᵘ p ℚᵘ.⊔ toℚᵘ q)
    rhs = ↥ᵘ (toℚᵘ p ℚᵘ.⊔ toℚᵘ q) ℤ.* ↧ (p ⊔ q)
    ↥p↧q = ↥ p ℤ.* ↧ q
    ↥q↧p = ↥ q ℤ.* ↧ p
    ↧p↧q = ↧ₙ p ℕ.* ↧ₙ q
    mul = gcd (↥p↧q ℤ.⊔ ↥q↧p) (+ ↧p↧q)
    mul≢0 : mul ≢ + 0
    mul≢0 = contraposition (gcd[i,j]≡0⇒j≡0 {↥p↧q ℤ.⊔ ↥q↧p} {+ ↧p↧q}) (ℕ.1+n≢0 ∘ ℤ.+-injective)

⊔-rawMagma : RawMagma _ _
⊔-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _⊔_
  }

toℚᵘ-isMagmaHomomorphism-⊔ : IsMagmaHomomorphism ⊔-rawMagma ℚᵘ.⊔-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-⊔ = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; homo = toℚᵘ-homo-⊔
  }

toℚᵘ-isMagmaMonomorphism-⊔ : IsMagmaMonomorphism ⊔-rawMagma ℚᵘ.⊔-rawMagma toℚᵘ
toℚᵘ-isMagmaMonomorphism-⊔ = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-⊔
  ; injective = toℚᵘ-injective
  }

⊔-⊓-rawLattice : RawLattice _ _
⊔-⊓-rawLattice = record
  { _≈_ = _≡_
  ; _∨_ = _⊔_
  ; _∧_ = _⊓_
  }

⊓-⊔-rawLattice : RawLattice _ _
⊓-⊔-rawLattice = record
  { _≈_ = _≡_
  ; _∨_ = _⊓_
  ; _∧_ = _⊔_
  }

toℚᵘ-isLatticeHomomorphism-⊔-⊓ : IsLatticeHomomorphism ⊔-⊓-rawLattice ℚᵘ.⊔-⊓-rawLattice toℚᵘ
toℚᵘ-isLatticeHomomorphism-⊔-⊓ = record
  { ∨-isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-⊔
  ; ∧-isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-⊓
  }

toℚᵘ-isLatticeMonomorphism-⊔-⊓ : IsLatticeMonomorphism ⊔-⊓-rawLattice ℚᵘ.⊔-⊓-rawLattice toℚᵘ
toℚᵘ-isLatticeMonomorphism-⊔-⊓ = record
  { isLatticeHomomorphism = toℚᵘ-isLatticeHomomorphism-⊔-⊓
  ; injective = toℚᵘ-injective
  }

private
  module ⊔-Monomorphism = MagmaMonomorphisms toℚᵘ-isMagmaMonomorphism-⊔
  module ⊔-⊓-Monomorphism = LatticeMonomorphisms toℚᵘ-isLatticeMonomorphism-⊔-⊓

------------------------------------------------------------------------
-- Algebraic properties

⊔-comm : Commutative _⊔_
⊔-comm = ⊔-Monomorphism.comm ℚᵘ.⊔-isMagma ℚᵘ.⊔-comm

⊔-assoc : Associative _⊔_
⊔-assoc = ⊔-Monomorphism.assoc ℚᵘ.⊔-isMagma ℚᵘ.⊔-assoc

⊔-idem : Idempotent _⊔_
⊔-idem = ⊔-Monomorphism.idem ℚᵘ.⊔-isMagma ℚᵘ.⊔-idem

⊔-sel : Selective _⊔_
⊔-sel = ⊔-Monomorphism.sel ℚᵘ.⊔-isMagma ℚᵘ.⊔-sel

------------------------------------------------------------------------
-- Other properties

p≤q⇒p⊔q≡q : ∀ {p q} → p ≤ q → p ⊔ q ≡ q
p≤q⇒p⊔q≡q {p} {q} p≤q = toℚᵘ-injective $ begin-equality
  toℚᵘ (p ⊔ q)                  ≈⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q            ≈⟨ ℚᵘ.p≤q⇒p⊔q≃q (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ q                        ∎
  where
    open ℚᵘ.≤-Reasoning

p⊔q≡q⇒p≤q : ∀ {p q} → p ⊔ q ≡ q → p ≤ q
p⊔q≡q⇒p≤q {p} {q} p⊔q≡q = toℚᵘ-cancel-≤ (ℚᵘ.p⊔q≃q⇒p≤q (begin-equality
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q ≈˘⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ (p ⊔ q)       ≡⟨ cong toℚᵘ p⊔q≡q ⟩
  toℚᵘ q             ∎))
  where
    open ℚᵘ.≤-Reasoning

q≤p⇒p⊔q≡p : ∀ {p q} → q ≤ p → p ⊔ q ≡ p
q≤p⇒p⊔q≡p {p} {q} q≤p = toℚᵘ-injective $ begin-equality
  toℚᵘ (p ⊔ q)                  ≈⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q            ≈⟨ ℚᵘ.q≤p⇒p⊔q≃p (toℚᵘ-mono-≤ q≤p) ⟩
  toℚᵘ p                        ∎
  where
    open ℚᵘ.≤-Reasoning

p⊔q≡p⇒q≤p : ∀ {p q} → p ⊔ q ≡ p → q ≤ p
p⊔q≡p⇒q≤p {p} {q} p⊔q≡p = toℚᵘ-cancel-≤ (ℚᵘ.p⊔q≃p⇒q≤p (begin-equality
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q            ≈˘⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ (p ⊔ q)                  ≡⟨ cong toℚᵘ p⊔q≡p ⟩
  toℚᵘ p                        ∎))
  where
    open ℚᵘ.≤-Reasoning

p⊔q≥p : ∀ p q → p ⊔ q ≥ p
p⊔q≥p p q = toℚᵘ-cancel-≤ $ begin
  toℚᵘ p                        ≤⟨ ℚᵘ.p⊔q≥p (toℚᵘ p) (toℚᵘ q) ⟩
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q            ≈˘⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ (p ⊔ q)                  ∎
  where
    open ℚᵘ.≤-Reasoning

p⊔q≥q : ∀ p q → p ⊔ q ≥ q
p⊔q≥q p q = toℚᵘ-cancel-≤ $ begin
  toℚᵘ q                        ≤⟨ ℚᵘ.p⊔q≥q (toℚᵘ p) (toℚᵘ q) ⟩
  toℚᵘ p ℚᵘ.⊔ toℚᵘ q            ≈˘⟨ toℚᵘ-homo-⊔ p q ⟩
  toℚᵘ (p ⊔ q)                  ∎
  where
    open ℚᵘ.≤-Reasoning

mono-≤-distrib-⊔ : ∀ f → f Preserves _≤_ ⟶ _≤_ → ∀ p q → f (p ⊔ q) ≡ f p ⊔ f q
mono-≤-distrib-⊔ f f-mono-≤ p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊔ q)                     ≡⟨ cong f (p≤q⇒p⊔q≡q (<⇒≤ p<q)) ⟩
  f q                           ≡˘⟨ p≤q⇒p⊔q≡q (f-mono-≤ (<⇒≤ p<q)) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊔ q)                     ≡⟨ cong f (⊔-idem p) ⟩
  f q                           ≡˘⟨ ⊔-idem (f p) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊔ q)                     ≡⟨ cong f (q≤p⇒p⊔q≡p (<⇒≤ p>q)) ⟩
  f p                           ≡˘⟨ q≤p⇒p⊔q≡p (f-mono-≤ (<⇒≤ p>q)) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning

mono-<-distrib-⊔ : ∀ f → f Preserves _<_ ⟶ _<_ → ∀ p q → f (p ⊔ q) ≡ f p ⊔ f q
mono-<-distrib-⊔ f f-mono-< p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊔ q)                     ≡⟨ cong f (p≤q⇒p⊔q≡q (<⇒≤ p<q)) ⟩
  f q                           ≡˘⟨ p≤q⇒p⊔q≡q (<⇒≤ (f-mono-< p<q)) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊔ q)                     ≡⟨ cong f (⊔-idem p) ⟩
  f q                           ≡˘⟨ ⊔-idem (f p) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊔ q)                     ≡⟨ cong f (q≤p⇒p⊔q≡p (<⇒≤ p>q)) ⟩
  f p                           ≡˘⟨ q≤p⇒p⊔q≡p (<⇒≤ (f-mono-< p>q)) ⟩
  f p ⊔ f q                     ∎
  where
    open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _⊔_ and _*_

*-distribˡ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊔ (p * r)
*-distribˡ-⊔-nonNeg p p≥0 q r = mono-≤-distrib-⊔ (p *_) (*-monoˡ-≤-nonNeg {p} p≥0) q r

*-distribʳ-⊔-nonNeg : ∀ p → NonNegative p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊔ (r * p)
*-distribʳ-⊔-nonNeg p p≥0 q r = mono-≤-distrib-⊔ (_* p) (*-monoʳ-≤-nonNeg {p} p≥0) q r

------------------------------------------------------------------------
-- Properties of _⊓_ and _⊔_

mono-≤-≥-distrib-⊓-⊔ : ∀ f → f Preserves _≤_ ⟶ _≥_ → ∀ p q → f (p ⊓ q) ≡ f p ⊔ f q
mono-≤-≥-distrib-⊓-⊔ f f-mono-≤ p q with <-cmp p q
... | tri< p<q p≢q  p≯q = begin
  f (p ⊓ q)                         ≡⟨ cong f (p≤q⇒p⊓q≡p (<⇒≤ p<q)) ⟩
  f p                               ≡˘⟨ q≤p⇒p⊔q≡p (f-mono-≤ (<⇒≤ p<q)) ⟩
  f p ⊔ f q                         ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊓ q)                         ≡⟨ cong f (⊓-idem p) ⟩
  f p                               ≡˘⟨ ⊔-idem (f p) ⟩
  f p ⊔ f q                         ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≢q  p>q = begin
  f (p ⊓ q)                         ≡⟨ cong f (q≤p⇒p⊓q≡q (<⇒≤ p>q)) ⟩
  f q                               ≡˘⟨ p≤q⇒p⊔q≡q (f-mono-≤ (<⇒≤ p>q)) ⟩
  f p ⊔ f q                         ∎
  where
    open ≡-Reasoning

mono-≤-≥-distrib-⊔-⊓ : ∀ f → f Preserves _≤_ ⟶ _≥_ → ∀ p q → f (p ⊔ q) ≡ f p ⊓ f q
mono-≤-≥-distrib-⊔-⊓ f f-mono-≤ p q with <-cmp p q
... | tri< p<q p≢q  p≯q = begin
  f (p ⊔ q)                         ≡⟨ cong f (p≤q⇒p⊔q≡q (<⇒≤ p<q)) ⟩
  f q                               ≡˘⟨ q≤p⇒p⊓q≡q (f-mono-≤ (<⇒≤ p<q)) ⟩
  f p ⊓ f q                         ∎
  where
    open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊔ q)                         ≡⟨ cong f (⊔-idem p) ⟩
  f p                               ≡˘⟨ ⊓-idem (f p) ⟩
  f p ⊓ f q                         ∎
  where
    open ≡-Reasoning
... | tri> p≮q p≢q  p>q = begin
  f (p ⊔ q)                         ≡⟨ cong f (q≤p⇒p⊔q≡p (<⇒≤ p>q)) ⟩
  f p                               ≡˘⟨ p≤q⇒p⊓q≡p (f-mono-≤ (<⇒≤ p>q)) ⟩
  f p ⊓ f q                         ∎
  where
    open ≡-Reasoning

⊔-absorbs-⊓ : _⊔_ Absorbs _⊓_
⊔-absorbs-⊓ = ⊔-⊓-Monomorphism.∨-absorbs-∧ ℚᵘ.⊔-⊓-isLattice

⊓-absorbs-⊔ : _⊓_ Absorbs _⊔_
⊓-absorbs-⊔ = ⊔-⊓-Monomorphism.∧-absorbs-∨ ℚᵘ.⊔-⊓-isLattice

⊔-⊓-absorptive : Absorptive _⊔_ _⊓_
⊔-⊓-absorptive = ⊔-⊓-Monomorphism.absorptive ℚᵘ.⊔-⊓-isLattice

⊓-⊔-absorptive : Absorptive _⊓_ _⊔_
⊓-⊔-absorptive = ⊓-absorbs-⊔ , ⊔-absorbs-⊓

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊔-nonPos-⊓ : ∀ p → NonPositive p → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊓ (p * r)
*-distribˡ-⊔-nonPos-⊓ p p≤0 = mono-≤-≥-distrib-⊔-⊓ (p *_) (*-monoˡ-≤-nonPos-≥ {p} p≤0)

*-distribʳ-⊔-nonPos-⊓ : ∀ p → NonPositive p → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊓ (r * p)
*-distribʳ-⊔-nonPos-⊓ p p≤0 = mono-≤-≥-distrib-⊔-⊓ (_* p) (*-monoʳ-≤-nonPos-≥ {p} p≤0)

*-distribˡ-⊓-nonPos-⊔ : ∀ p → NonPositive p → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊔ (p * r)
*-distribˡ-⊓-nonPos-⊔ p p≤0 = mono-≤-≥-distrib-⊓-⊔ (p *_) (*-monoˡ-≤-nonPos-≥ {p} p≤0)

*-distribʳ-⊓-nonPos-⊔ : ∀ p → NonPositive p → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊔ (r * p)
*-distribʳ-⊓-nonPos-⊔ p p≤0 = mono-≤-≥-distrib-⊓-⊔ (_* p) (*-monoʳ-≤-nonPos-≥ {p} p≤0)

------------------------------------------------------------------------
-- Structures

⊔-isMagma : IsMagma _⊔_
⊔-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = cong₂ _⊔_
  }

⊔-isSemigroup : IsSemigroup _⊔_
⊔-isSemigroup = record
  { isMagma = ⊔-isMagma
  ; assoc = ⊔-assoc
  }

⊔-isBand : IsBand _⊔_
⊔-isBand = record
  { isSemigroup = ⊔-isSemigroup
  ; idem = ⊔-idem
  }

⊔-isCommutativeSemigroup : IsCommutativeSemigroup _⊔_
⊔-isCommutativeSemigroup = record
  { isSemigroup = ⊔-isSemigroup
  ; comm = ⊔-comm
  }

⊔-isSemilattice : IsSemilattice _⊔_
⊔-isSemilattice = record
  { isBand = ⊔-isBand
  ; comm = ⊔-comm
  }

⊔-isSelectiveMagma : IsSelectiveMagma _⊔_
⊔-isSelectiveMagma = record
  { isMagma = ⊔-isMagma
  ; sel = ⊔-sel
  }

⊔-⊓-isLattice : IsLattice _⊔_ _⊓_
⊔-⊓-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm = ⊔-comm
  ; ∨-assoc = ⊔-assoc
  ; ∨-cong = cong₂ _⊔_
  ; ∧-comm = ⊓-comm
  ; ∧-assoc = ⊓-assoc
  ; ∧-cong = cong₂ _⊓_
  ; absorptive = ⊔-⊓-absorptive
  }

⊓-⊔-isLattice : IsLattice _⊓_ _⊔_
⊓-⊔-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm = ⊓-comm
  ; ∨-assoc = ⊓-assoc
  ; ∨-cong = cong₂ _⊓_
  ; ∧-comm = ⊔-comm
  ; ∧-assoc = ⊔-assoc
  ; ∧-cong = cong₂ _⊔_
  ; absorptive = ⊓-⊔-absorptive
  }

------------------------------------------------------------------------
-- Bundles

⊔-magma : Magma _ _
⊔-magma = record
  { isMagma = ⊔-isMagma
  }

⊔-semigroup : Semigroup _ _
⊔-semigroup = record
  { isSemigroup = ⊔-isSemigroup
  }

⊔-band : Band _ _
⊔-band = record
  { isBand = ⊔-isBand
  }

⊔-commutativeSemigroup : CommutativeSemigroup _ _
⊔-commutativeSemigroup = record
  { isCommutativeSemigroup = ⊔-isCommutativeSemigroup
  }

⊔-semilattice : Semilattice _ _
⊔-semilattice = record
  { isSemilattice = ⊔-isSemilattice
  }

⊔-selectiveMagma : SelectiveMagma _ _
⊔-selectiveMagma = record
  { isSelectiveMagma = ⊔-isSelectiveMagma
  }

⊔-⊓-lattice : Lattice _ _
⊔-⊓-lattice = record
  { isLattice = ⊔-⊓-isLattice
  }

⊓-⊔-lattice : Lattice _ _
⊓-⊔-lattice = record
  { isLattice = ⊓-⊔-isLattice
  }

------------------------------------------------------------------------
-- Properties of 1/_
------------------------------------------------------------------------

positive⇒1/positive : ∀ q → (q>0 : Positive q) → Positive ((1/ q) {Dec.fromWitnessFalse (contraposition ℤ.∣n∣≡0⇒n≡0 (≢-sym (ℤ.<⇒≢ (ℤ.positive⁻¹ q>0))))})
positive⇒1/positive (mkℚ +[1+ n ] d-1 _) _ = tt

negative⇒1/negative : ∀ q → (q<0 : Negative q) → Negative ((1/ q) {Dec.fromWitnessFalse (contraposition ℤ.∣n∣≡0⇒n≡0 (ℤ.<⇒≢ (ℤ.negative⁻¹ q<0)))})
negative⇒1/negative (mkℚ -[1+ n ] d-1 _) _ = tt

1/q≢0 : ∀ q {q≢0} → ℤ.∣ (↥ ((1/ q) {q≢0})) ∣ ≢0
1/q≢0 (mkℚ (+[1+ n ]) d-1 _) = tt
1/q≢0 (mkℚ (-[1+ n ]) d-1 _) = tt

1/-involutive : ∀ q {q≢0} → (1/ (1/ q) {q≢0}) {1/q≢0 q {q≢0}} ≡ q
1/-involutive (mkℚ +[1+ n ] d-1 _) = refl
1/-involutive (mkℚ -[1+ n ] d-1 _) = refl

1/positive⇒positive : ∀ q {q≢0} → (1/q : Positive ((1/ q) {q≢0})) → Positive q
1/positive⇒positive q {q≢0} 1/q>0 = subst Positive (1/-involutive q {q≢0}) (positive⇒1/positive (1/ q) 1/q>0)

1/negative⇒negative : ∀ q {q≢0} → (1/q : Negative ((1/ q) {q≢0})) → Negative q
1/negative⇒negative q {q≢0} 1/q>0 = subst Negative (1/-involutive q {q≢0}) (negative⇒1/negative (1/ q) 1/q>0)

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Monomorphic to unnormalised -_

toℚᵘ-homo-∣_∣ : Homomorphic₁ toℚᵘ ∣_∣ ℚᵘ.∣_∣
toℚᵘ-homo-∣ mkℚ +[1+ n ] d-1 isCoprime ∣ = *≡* refl
toℚᵘ-homo-∣ mkℚ (+ zero) d-1 isCoprime ∣ = *≡* refl
toℚᵘ-homo-∣ mkℚ -[1+ n ] d-1 isCoprime ∣ = *≡* refl

------------------------------------------------------------------------
-- Properties

∣p∣≡p⇒p≡0 : ∀ p → ∣ p ∣ ≡ 0ℚ → p ≡ 0ℚ
∣p∣≡p⇒p≡0 (mkℚ (+_ zero) zero _) ∣p∣≡0 = refl

0≤∣p∣ : ∀ p → 0ℚ ≤ ∣ p ∣
0≤∣p∣ p = *≤* (begin
  (↥ 0ℚ) ℤ.* (↧ ∣ p ∣)                                      ≡⟨ ℤ.*-zeroˡ (↧ ∣ p ∣) ⟩
  0ℤ                                                        ≤⟨ ℤ.+≤+ ℕ.z≤n ⟩
  ↥ ∣ p ∣                                                   ≡˘⟨ ℤ.*-identityʳ (↥ ∣ p ∣) ⟩
  ↥ ∣ p ∣ ℤ.* 1ℤ                                            ∎)
  where
    open ℤ.≤-Reasoning

∣-p∣≡∣p∣ : ∀ p → ∣ - p ∣ ≡ ∣ p ∣
∣-p∣≡∣p∣ (mkℚ +[1+ n ] d-1 _) = refl
∣-p∣≡∣p∣ (mkℚ (+ zero) d-1 _) = refl
∣-p∣≡∣p∣ (mkℚ -[1+ n ] d-1 _) = refl

∣p∣≡p⊎∣p∣≡-p : ∀ p → ∣ p ∣ ≡ p ⊎ ∣ p ∣ ≡ - p
∣p∣≡p⊎∣p∣≡-p (mkℚ (+ n) d-1 _) = inj₁ refl
∣p∣≡p⊎∣p∣≡-p (mkℚ (-[1+ n ]) d-1 _) = inj₂ refl

0≤p⇒∣p∣≡p : ∀ {p} → 0ℚ ≤ p → ∣ p ∣ ≡ p
0≤p⇒∣p∣≡p {p} 0≤p = toℚᵘ-injective (ℚᵘ.0≤p⇒∣p∣≃p (toℚᵘ-mono-≤ 0≤p))

∣p+q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p+q∣≤∣p∣+∣q∣ p q = toℚᵘ-cancel-≤ (begin
  toℚᵘ ∣ p + q ∣                                            ≈⟨ toℚᵘ-homo-∣ (p + q) ∣ ⟩
  ℚᵘ.∣ toℚᵘ (p + q) ∣                                       ≈⟨ ℚᵘ.∣ (toℚᵘ-homo-+ p q) ∣-cong ⟩
  ℚᵘ.∣ toℚᵘ p ℚᵘ.+ toℚᵘ q ∣                                 ≤⟨ ℚᵘ.∣p+q∣≤∣p∣+∣q∣ (toℚᵘ p) (toℚᵘ q) ⟩
  ℚᵘ.∣ toℚᵘ p ∣ ℚᵘ.+ ℚᵘ.∣ toℚᵘ q ∣                          ≈˘⟨ ℚᵘ.+-cong toℚᵘ-homo-∣ p ∣ toℚᵘ-homo-∣ q ∣ ⟩
  toℚᵘ ∣ p ∣ ℚᵘ.+ toℚᵘ ∣ q ∣                                ≈˘⟨ toℚᵘ-homo-+ ∣ p ∣ ∣ q ∣ ⟩
  toℚᵘ (∣ p ∣ + ∣ q ∣)                                      ∎)
  where
    open ℚᵘ.≤-Reasoning

∣p-q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p-q∣≤∣p∣+∣q∣ p q = begin
  ∣ p   -     q ∣                                           ≤⟨ ∣p+q∣≤∣p∣+∣q∣ p (- q) ⟩
  ∣ p ∣ + ∣ - q ∣                                           ≡⟨ cong (λ h → ∣ p ∣ + h) (∣-p∣≡∣p∣ q) ⟩
  ∣ p ∣ + ∣   q ∣                                           ∎
  where
    open ≤-Reasoning

∣p*q∣≡∣p∣*∣q∣ : ∀ p q → ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
∣p*q∣≡∣p∣*∣q∣ p q = toℚᵘ-injective (begin-equality
  toℚᵘ ∣ p * q ∣                                            ≈⟨ toℚᵘ-homo-∣ (p * q) ∣ ⟩
  ℚᵘ.∣ toℚᵘ (p * q) ∣                                       ≈⟨ ℚᵘ.∣ (toℚᵘ-homo-* p q) ∣-cong ⟩
  ℚᵘ.∣ toℚᵘ p ℚᵘ.* toℚᵘ q ∣                                 ≈⟨ ℚᵘ.∣p*q∣≃∣p∣*∣q∣ (toℚᵘ p) (toℚᵘ q) ⟩
  ℚᵘ.∣ toℚᵘ p ∣ ℚᵘ.* ℚᵘ.∣ toℚᵘ q ∣                          ≈˘⟨ ℚᵘ.*-cong toℚᵘ-homo-∣ p ∣ toℚᵘ-homo-∣ q ∣ ⟩
  toℚᵘ ∣ p ∣ ℚᵘ.* toℚᵘ ∣ q ∣                                ≈˘⟨ toℚᵘ-homo-* ∣ p ∣ ∣ q ∣ ⟩
  toℚᵘ (∣ p ∣ * ∣ q ∣)                                      ∎)
  where
    open ℚᵘ.≤-Reasoning

nonNegative[∣p∣] : ∀ p → NonNegative ∣ p ∣
nonNegative[∣p∣] (mkℚ +[1+ n ] d-1 _) = tt
nonNegative[∣p∣] (mkℚ (+ zero) d-1 _) = tt
nonNegative[∣p∣] (mkℚ -[1+ n ] d-1 _) = tt

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

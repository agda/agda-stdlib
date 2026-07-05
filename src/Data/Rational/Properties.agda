------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --warning=noUserWarning #-} -- for +-rawMonoid, *-rawMonoid (issue #1865, #1844, #1755)

module Data.Rational.Properties where

open import Algebra.Apartness
  using (IsHeytingCommutativeRing; IsHeytingField
        ; HeytingCommutativeRing; HeytingField)
open import Algebra.Construct.NaturalChoice.Base
  using (MinOperator; MaxOperator)
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
open import Algebra.Morphism
open import Algebra.Bundles
import Algebra.Morphism.MagmaMonomorphism  as MagmaMonomorphisms
import Algebra.Morphism.MonoidMonomorphism as MonoidMonomorphisms
import Algebra.Morphism.GroupMonomorphism  as GroupMonomorphisms
import Algebra.Morphism.RingMonomorphism   as RingMonomorphisms
import Algebra.Lattice.Morphism.LatticeMonomorphism as LatticeMonomorphisms
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
import Algebra.Properties.Group as GroupProperties
open import Data.Bool.Base using (T; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; +[1+_]; +0; 0ℤ; 1ℤ; _◃_)
open import Data.Integer.Coprimality using (coprime-divisor)
import Data.Integer.Properties as ℤ
open import Data.Integer.GCD using (gcd; gcd[i,j]≡0⇒i≡0; gcd[i,j]≡0⇒j≡0; gcd-zeroʳ)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤ-solver)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Nat.Coprimality as C using (Coprime; coprime?)
open import Data.Nat.Divisibility using (_∣_; divides; ∣-antisym; *-pres-∣)
import Data.Nat.GCD as ℕ
import Data.Nat.DivMod as ℕ
open import Data.Product.Base using (proj₁; proj₂; _×_; _,_; uncurry)
open import Data.Rational.Base
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; mkℚᵘ; *≡*; *≤*; *<*)
  renaming
  ( ↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_; ↧ₙ_ to ↧ₙᵘ_
  ; _≃_ to _≃ᵘ_; _≤_ to _≤ᵘ_; _<_ to _<ᵘ_
  ; _+_ to _+ᵘ_)
import Data.Rational.Unnormalised.Properties as ℚᵘ
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′; _⊎_)
import Data.Sign.Base as Sign
open import Function.Base using (_∘_; _∘′_; _∘₂_; _$_; flip)
open import Function.Definitions using (Congruent; Injective)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism
        ; IsOrderHomomorphism; IsOrderMonomorphism)
import Relation.Binary.Morphism.OrderMonomorphism as OrderMonomorphisms
import Relation.Binary.Properties.DecSetoid as DecSetoidProperties
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; sym; trans; _≢_; subst; subst₂; resp₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid; decSetoid; module ≡-Reasoning; isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Reasoning.Syntax using (module ≃-syntax)
open import Relation.Nullary.Decidable.Core as Dec
  using (yes; no; recompute; map′; _×-dec_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

open import Algebra.Definitions {A = ℚ} _≡_
open import Algebra.Structures  {A = ℚ} _≡_

private
  variable
    p q r : ℚ

------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

mkℚ-cong : ∀ {n₁ n₂ d₁ d₂}
           .{c₁ : Coprime ℤ.∣ n₁ ∣ (suc d₁)}
           .{c₂ : Coprime ℤ.∣ n₂ ∣ (suc d₂)} →
           n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
mkℚ-cong refl refl = refl

mkℚ-injective : ∀ {n₁ n₂ d₁ d₂}
                .{c₁ : Coprime ℤ.∣ n₁ ∣ (suc d₁)}
                .{c₂ : Coprime ℤ.∣ n₂ ∣ (suc d₂)} →
                mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂ → n₁ ≡ n₂ × d₁ ≡ d₂
mkℚ-injective refl = refl , refl

infix 4 _≡?_

_≡?_ : DecidableEquality ℚ
mkℚ n₁ d₁ _ ≡? mkℚ n₂ d₂ _ = map′
  (uncurry mkℚ-cong)
  mkℚ-injective
  (n₁ ℤ.≡? n₂ ×-dec d₁ ℕ.≡? d₂)

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ℚ

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≡?_

1≢0 : 1ℚ ≢ 0ℚ
1≢0 = λ ()

------------------------------------------------------------------------
-- mkℚ+
------------------------------------------------------------------------

mkℚ+-cong : ∀ {n₁ n₂ d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
           .{c₁ : Coprime n₁ d₁}
           .{c₂ : Coprime n₂ d₂} →
           n₁ ≡ n₂ → d₁ ≡ d₂ →
           mkℚ+ n₁ d₁ c₁ ≡ mkℚ+ n₂ d₂ c₂
mkℚ+-cong refl refl = refl

mkℚ+-injective : ∀ {n₁ n₂ d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
           .{c₁ : Coprime n₁ d₁}
           .{c₂ : Coprime n₂ d₂} →
           mkℚ+ n₁ d₁ c₁ ≡ mkℚ+ n₂ d₂ c₂ →
           n₁ ≡ n₂ × d₁ ≡ d₂
mkℚ+-injective {d₁ = suc _} {suc _} refl = refl , refl

↥-mkℚ+ : ∀ n d .{{_ : ℕ.NonZero d}} .{c : Coprime n d} → ↥ (mkℚ+ n d c) ≡ + n
↥-mkℚ+ n (suc d) = refl

↧-mkℚ+ : ∀ n d .{{_ : ℕ.NonZero d}} .{c : Coprime n d} → ↧ (mkℚ+ n d c) ≡ + d
↧-mkℚ+ n (suc d) = refl

mkℚ+-nonNeg : ∀ n d .{{_ : ℕ.NonZero d}} .{c : Coprime n d} →
              NonNegative (mkℚ+ n d c)
mkℚ+-nonNeg n (suc d) = _

mkℚ+-pos : ∀ n d .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero d}}
           .{c : Coprime n d} → Positive (mkℚ+ n d c)
mkℚ+-pos (suc n) (suc d) = _

------------------------------------------------------------------------
-- Numerator and denominator equality
------------------------------------------------------------------------

drop-*≡* : p ≃ q → ↥ p ℤ.* ↧ q ≡ ↥ q ℤ.* ↧ p
drop-*≡* (*≡* eq) = eq

≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = *≡* refl

≃⇒≡ : _≃_ ⇒ _≡_
≃⇒≡ {x = mkℚ n₁ d₁ c₁} {y = mkℚ n₂ d₂ c₂} (*≡* eq) = helper
  where
  open ≡-Reasoning

  1+d₁∣1+d₂ : suc d₁ ∣ suc d₂
  1+d₁∣1+d₂ = coprime-divisor (+ suc d₁) n₁ (+ suc d₂)
    (C.sym (C.recompute c₁)) $
    divides ℤ.∣ n₂ ∣ $ begin
      ℤ.∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ cong ℤ.∣_∣ eq ⟩
      ℤ.∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ ℤ.abs-* n₂ (+ suc d₁) ⟩
      ℤ.∣ n₂ ∣ ℕ.* suc d₁    ∎

  1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
  1+d₂∣1+d₁ = coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
    (C.sym (C.recompute c₂)) $
    divides ℤ.∣ n₁ ∣ (begin
      ℤ.∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ cong ℤ.∣_∣ (sym eq) ⟩
      ℤ.∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ ℤ.abs-* n₁ (+ suc d₂) ⟩
      ℤ.∣ n₁ ∣ ℕ.* suc d₂    ∎)

  helper : mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
  helper with refl ← ∣-antisym 1+d₁∣1+d₂ 1+d₂∣1+d₁
         with refl ← ℤ.*-cancelʳ-≡ n₁ n₂ (+ suc d₁) eq
    = refl

≃-sym : Symmetric _≃_
≃-sym = ≡⇒≃ ∘′ sym ∘′ ≃⇒≡

------------------------------------------------------------------------
-- Properties of ↥
------------------------------------------------------------------------

↥p≡0⇒p≡0 : ∀ p → ↥ p ≡ 0ℤ → p ≡ 0ℚ
↥p≡0⇒p≡0 (mkℚ +0 d-1 0-coprime-d) ↥p≡0 = mkℚ-cong refl d-1≡0
  where d-1≡0 = ℕ.suc-injective (C.0-coprimeTo-m⇒m≡1 (C.recompute 0-coprime-d))

p≡0⇒↥p≡0 : ∀ p → p ≡ 0ℚ → ↥ p ≡ 0ℤ
p≡0⇒↥p≡0 p refl = refl

0≡?-weak : (p : ℚ) → Maybe (0ℚ ≡ p)
0≡?-weak p with ↥ p ℤ.≟ 0ℤ
... | yes ↥p≡0 = just (sym (↥p≡0⇒p≡0 p ↥p≡0))
... | no  _    = nothing

↥p≡↥q≡0⇒p≡q : ∀ p q → ↥ p ≡ 0ℤ → ↥ q ≡ 0ℤ → p ≡ q
↥p≡↥q≡0⇒p≡q p q ↥p≡0 ↥q≡0 = trans (↥p≡0⇒p≡0 p ↥p≡0) (sym (↥p≡0⇒p≡0 q ↥q≡0))

------------------------------------------------------------------------
-- Basic properties of sign predicates
------------------------------------------------------------------------

nonNeg≢neg : ∀ p q → .{{NonNegative p}} → .{{Negative q}} → p ≢ q
nonNeg≢neg (mkℚ (+ _) _ _) (mkℚ -[1+ _ ] _ _) ()

pos⇒nonNeg : ∀ p → .{{Positive p}} → NonNegative p
pos⇒nonNeg p = ℚᵘ.pos⇒nonNeg (toℚᵘ p)

neg⇒nonPos : ∀ p → .{{Negative p}} → NonPositive p
neg⇒nonPos p = ℚᵘ.neg⇒nonPos (toℚᵘ p)

nonNeg∧nonZero⇒pos : ∀ p → .{{NonNegative p}} → .{{NonZero p}} → Positive p
nonNeg∧nonZero⇒pos (mkℚ +[1+ _ ] _ _) = _

pos⇒nonZero : ∀ p → .{{Positive p}} → NonZero p
pos⇒nonZero (mkℚ +[1+ _ ] _ _) = _

neg⇒nonZero : ∀ p → .{{Negative p}} → NonZero p
neg⇒nonZero (mkℚ -[1+ _ ] _ _) = _

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

neg-injective : - p ≡ - q → p ≡ q
neg-injective {mkℚ +[1+ m ] _ _} {mkℚ +[1+ n ] _ _} refl = refl
neg-injective {mkℚ +0       _ _} {mkℚ +0       _ _} refl = refl
neg-injective {mkℚ -[1+ m ] _ _} {mkℚ -[1+ n ] _ _} refl = refl
neg-injective {mkℚ +[1+ m ] _ _} {mkℚ -[1+ n ] _ _} ()
neg-injective {mkℚ +0       _ _} {mkℚ -[1+ n ] _ _} ()
neg-injective {mkℚ -[1+ m ] _ _} {mkℚ +[1+ n ] _ _} ()
neg-injective {mkℚ -[1+ m ] _ _} {mkℚ +0       _ _} ()

neg-pos : Positive p → Negative (- p)
neg-pos {mkℚ +[1+ _ ] _ _} _ = _

------------------------------------------------------------------------
-- Properties of normalize
------------------------------------------------------------------------

normalize-coprime : ∀ {n d-1} .(c : Coprime n (suc d-1)) →
                    normalize n (suc d-1) ≡ mkℚ (+ n) d-1 c
normalize-coprime {n} {d-1} c = begin
  normalize n d                                  ≡⟨⟩
  mkℚ+ ((n ℕ./ g) {{g≢0}}) ((d ℕ./ g) {{g≢0}}) _ ≡⟨ mkℚ+-cong {c₂ = c₂} (ℕ./-congʳ {{g≢0}} g≡1) (ℕ./-congʳ {{g≢0}} g≡1) ⟩
  mkℚ+ (n ℕ./ 1) (d ℕ./ 1) _                     ≡⟨ mkℚ+-cong {c₂ = c} (ℕ.n/1≡n n) (ℕ.n/1≡n d) ⟩
  mkℚ+ n d _                                     ≡⟨⟩
  mkℚ (+ n) d-1 _                                ∎
  where
  open ≡-Reasoning; d = suc d-1; g = ℕ.gcd n d
  c′ = C.recompute c
  c₂ : Coprime (n ℕ./ 1) (d ℕ./ 1)
  c₂ = subst₂ Coprime (sym (ℕ.n/1≡n n)) (sym (ℕ.n/1≡n d)) c′
  g≡1 = C.coprime⇒gcd≡1 c′
  instance
    g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 n d (inj₂ λ()))
    n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 n d {{_}} {{g≢0}})
    d/1≢0 = ℕ.≢-nonZero (subst (_≢ 0) (sym (ℕ.n/1≡n d)) λ())

↥-normalize : ∀ i n .{{_ : ℕ.NonZero n}} → ↥ (normalize i n) ℤ.* gcd (+ i) (+ n) ≡ + i
↥-normalize i n = begin
  ↥ (normalize i n) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↥-mkℚ+ _ (n ℕ./ g)) ⟩
  + i/g     ℤ.* + g          ≡⟨⟩
  Sign.+ ◃ i/g ℕ.* g         ≡⟨ cong (Sign.+ ◃_) (ℕ.m/n*n≡m (ℕ.gcd[m,n]∣m i n)) ⟩
  Sign.+ ◃ i                 ≡⟨ ℤ.+◃n≡+n i ⟩
  + i                        ∎
  where
  open ≡-Reasoning
  g     = ℕ.gcd i n
  instance g≢0 = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 i n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
  instance n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 i n {{gcd≢0 = g≢0}})
  i/g = (i ℕ./ g) {{g≢0}}

↧-normalize : ∀ i n .{{_ : ℕ.NonZero n}} → ↧ (normalize i n) ℤ.* gcd (+ i) (+ n) ≡ + n
↧-normalize i n = begin
  ↧ (normalize i n) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↧-mkℚ+ _ (n ℕ./ g)) ⟩
  + (n ℕ./ g)       ℤ.* + g  ≡⟨⟩
  Sign.+ ◃ n ℕ./ g     ℕ.* g ≡⟨ cong (Sign.+ ◃_) (ℕ.m/n*n≡m (ℕ.gcd[m,n]∣n i n)) ⟩
  Sign.+ ◃ n                 ≡⟨ ℤ.+◃n≡+n n ⟩
  + n                        ∎
  where
  open ≡-Reasoning
  g = ℕ.gcd i n
  instance g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0   i n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
  instance n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 i n {{gcd≢0 = g≢0}})

normalize-cong : ∀ {m₁ n₁ m₂ n₂} .{{_ : ℕ.NonZero n₁}} .{{_ : ℕ.NonZero n₂}} →
                 m₁ ≡ m₂ → n₁ ≡ n₂ → normalize m₁ n₁ ≡ normalize m₂ n₂
normalize-cong {m} {n} refl refl =
  mkℚ+-cong (ℕ./-congʳ {n = g} refl) (ℕ./-congʳ {n = g} refl)
  where
  g = ℕ.gcd m n
  instance
    g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
    n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})

normalize-nonNeg : ∀ m n .{{_ : ℕ.NonZero n}} → NonNegative (normalize m n)
normalize-nonNeg m n = mkℚ+-nonNeg (m ℕ./ g) (n ℕ./ g)
  where
  g = ℕ.gcd m n
  instance
    g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
    n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})

normalize-pos : ∀ m n .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero m}} → Positive (normalize m n)
normalize-pos m n = mkℚ+-pos (m ℕ./ ℕ.gcd m n) (n ℕ./ ℕ.gcd m n)
  where
  g = ℕ.gcd m n
  instance
    g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
    n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})
    m/g≢0 = ℕ.≢-nonZero (ℕ.m/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})

normalize-injective-≃ : ∀ m n c d {{_ : ℕ.NonZero c}} {{_ : ℕ.NonZero d}} →
                        normalize m c ≡ normalize n d →
                        m ℕ.* d ≡ n ℕ.* c
normalize-injective-≃ m n c d eq = ℕ./-cancelʳ-≡
  md∣gcd[m,c]gcd[n,d]
  nc∣gcd[m,c]gcd[n,d]
  $ begin
    (m ℕ.* d) ℕ./ (gcd[m,c] ℕ.* gcd[n,d]) ≡⟨  ℕ./-*-interchange gcd[m,c]∣m gcd[n,d]∣d ⟩
    (m ℕ./ gcd[m,c]) ℕ.* (d ℕ./ gcd[n,d]) ≡⟨  cong₂ ℕ._*_ m/gcd[m,c]≡n/gcd[n,d] (sym c/gcd[m,c]≡d/gcd[n,d]) ⟩
    (n ℕ./ gcd[n,d]) ℕ.* (c ℕ./ gcd[m,c]) ≡⟨ ℕ./-*-interchange gcd[n,d]∣n gcd[m,c]∣c ⟨
    (n ℕ.* c) ℕ./ (gcd[n,d] ℕ.* gcd[m,c]) ≡⟨ ℕ./-congʳ (ℕ.*-comm gcd[n,d] gcd[m,c]) ⟩
    (n ℕ.* c) ℕ./ (gcd[m,c] ℕ.* gcd[n,d]) ∎
  where
  open ≡-Reasoning
  gcd[m,c]   = ℕ.gcd m c
  gcd[n,d]   = ℕ.gcd n d
  gcd[m,c]∣m = ℕ.gcd[m,n]∣m m c
  gcd[m,c]∣c = ℕ.gcd[m,n]∣n m c
  gcd[n,d]∣n = ℕ.gcd[m,n]∣m n d
  gcd[n,d]∣d = ℕ.gcd[m,n]∣n n d
  md∣gcd[m,c]gcd[n,d] = *-pres-∣ gcd[m,c]∣m gcd[n,d]∣d
  nc∣gcd[n,d]gcd[m,c] = *-pres-∣ gcd[n,d]∣n gcd[m,c]∣c
  nc∣gcd[m,c]gcd[n,d] = subst (_∣ n ℕ.* c) (ℕ.*-comm gcd[n,d] gcd[m,c]) nc∣gcd[n,d]gcd[m,c]

  gcd[m,c]≢0′          = ℕ.gcd[m,n]≢0 m c (inj₂ (ℕ.≢-nonZero⁻¹ c))
  gcd[n,d]≢0′          = ℕ.gcd[m,n]≢0 n d (inj₂ (ℕ.≢-nonZero⁻¹ d))
  instance
    gcd[m,c]≢0   = ℕ.≢-nonZero gcd[m,c]≢0′
    gcd[n,d]≢0   = ℕ.≢-nonZero gcd[n,d]≢0′
    c/gcd[m,c]≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 m c {{gcd≢0 = gcd[m,c]≢0}})
    d/gcd[n,d]≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 n d {{gcd≢0 = gcd[n,d]≢0}})
    gcd[m,c]*gcd[n,d]≢0 = ℕ.m*n≢0 gcd[m,c] gcd[n,d]
    gcd[n,d]*gcd[m,c]≢0 = ℕ.m*n≢0 gcd[n,d] gcd[m,c]

  div = mkℚ+-injective eq
  m/gcd[m,c]≡n/gcd[n,d] = proj₁ div
  c/gcd[m,c]≡d/gcd[n,d] = proj₂ div

------------------------------------------------------------------------
-- Properties of _/_
------------------------------------------------------------------------

↥-/ : ∀ i n .{{_ : ℕ.NonZero n}} → ↥ (i / n) ℤ.* gcd i (+ n) ≡ i
↥-/ (+ m)    n = ↥-normalize m n
↥-/ -[1+ m ] n = begin-equality
  ↥ (- norm)   ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↥-neg norm) ⟩
  ℤ.- (↥ norm) ℤ.* + g  ≡⟨ sym (ℤ.neg-distribˡ-* (↥ norm) (+ g)) ⟩
  ℤ.- (↥ norm  ℤ.* + g) ≡⟨ cong (ℤ.-_) (↥-normalize (suc m) n) ⟩
  Sign.- ◃ suc m        ≡⟨⟩
  -[1+ m ]              ∎
  where
  open ℤ.≤-Reasoning
  g    = ℕ.gcd (suc m) n
  norm = normalize (suc m) n

↧-/ : ∀ i n .{{_ : ℕ.NonZero n}} → ↧ (i / n) ℤ.* gcd i (+ n) ≡ + n
↧-/ (+ m)    n = ↧-normalize m n
↧-/ -[1+ m ] n = begin-equality
  ↧ (- norm) ℤ.* + g  ≡⟨ cong (ℤ._* + g) (↧-neg norm) ⟩
  ↧ norm     ℤ.* + g  ≡⟨ ↧-normalize (suc m) n ⟩
  + n                 ∎
  where
  open ℤ.≤-Reasoning
  g    = ℕ.gcd (suc m) n
  norm = normalize (suc m) n

↥p/↧p≡p : ∀ p → ↥ p / ↧ₙ p ≡ p
↥p/↧p≡p (mkℚ (+ n)    d-1 prf) = normalize-coprime prf
↥p/↧p≡p (mkℚ -[1+ n ] d-1 prf) = cong (-_) (normalize-coprime prf)

↥[i/1]≡i : (i : ℤ) → ↥ (i / 1) ≡ i
↥[i/1]≡i i = begin
    ↥ (i / 1)              ≡⟨ ℤ.*-identityʳ (↥ (i / 1)) ⟨
    ↥ (i / 1) ℤ.* 1ℤ       ≡⟨ cong (↥ (i / 1) ℤ.*_) $ gcd-zeroʳ i ⟨
    ↥ (i / 1) ℤ.* gcd i 1ℤ ≡⟨ ↥-/ i 1 ⟩
    i                      ∎
  where open ≡-Reasoning


↧ₙ[i/1]≡1 : (i : ℤ) → ↧ₙ (i / 1) ≡ 1
↧ₙ[i/1]≡1 i = ℤ.+-injective $ begin
    ↧ (i / 1)               ≡⟨ ℤ.*-identityʳ (↧ (i / 1)) ⟨
    ↧ (i / 1) ℤ.* 1ℤ        ≡⟨ cong (↧ (i / 1) ℤ.*_) $ gcd-zeroʳ i ⟨
    ↧ (i / 1) ℤ.* gcd i 1ℤ  ≡⟨ ↧-/ i 1 ⟩
    1ℤ                      ∎
  where open ≡-Reasoning

0/n≡0 : ∀ n .{{_ : ℕ.NonZero n}} → 0ℤ / n ≡ 0ℚ
0/n≡0 n@(suc n-1) {{n≢0}} = mkℚ+-cong {{n/n≢0}} {c₂ = 0-cop-1} (ℕ.0/n≡0 (ℕ.gcd 0 n)) (ℕ.n/n≡1 n)
  where
  0-cop-1 = C.sym (C.1-coprimeTo 0)
  n/n≢0   = ℕ.>-nonZero (subst (ℕ._> 0) (sym (ℕ.n/n≡1 n)) (ℕ.z<s))

n/n≡1 : ∀ (n : ℕ) .{{_ : ℕ.NonZero n}} → + n / n ≡ 1ℚ
n/n≡1 n {{nz}} = mkℚ+-cong n/gcd[n,n]≡1 n/gcd[n,n]≡1
  where
  instance g≢0   = ℕ.≢-nonZero (ℕ.gcd[m,n]≢0 n n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
           n/g≢0 = ℕ.≢-nonZero (ℕ.n/gcd[m,n]≢0 n n {{gcd≢0 = g≢0}})
  n/gcd[n,n]≡1 = trans (ℕ./-congʳ {ℕ.gcd n n} (ℕ.gcd[n,n]≡n n)) (ℕ.n/n≡1 n {{nz}})

-i/n≡-[i/n] : ∀ (i : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n}} →
              ℤ.- i / n ≡ - (i / n)
-i/n≡-[i/n] +0       n = trans (0/n≡0 n) (cong -_ (sym (0/n≡0 n)))
-i/n≡-[i/n] +[1+ m ] n = refl
-i/n≡-[i/n] -[1+ m ] n
  with +[1+ m ] / n
... | mkℚ -[1+ a ] d prf = refl
... | mkℚ +0       d prf = refl
... | mkℚ +[1+ a ] d prf = refl

/-cong : ∀ {p₁ q₁ p₂ q₂} .{{_ : ℕ.NonZero q₁}} .{{_ : ℕ.NonZero q₂}} →
         p₁ ≡ p₂ → q₁ ≡ q₂ → p₁ / q₁ ≡ p₂ / q₂
/-cong {+ n}       refl = normalize-cong {n} refl
/-cong { -[1+ n ]} refl = cong -_ ∘′ normalize-cong {suc n} refl

private
  /-injective-≃-helper : ∀ {m n c d} .{{_ : ℕ.NonZero c}} .{{_ : ℕ.NonZero d}} →
                         - normalize (suc m) c ≡ normalize n d →
                          mkℚᵘ -[1+ m ] (ℕ.pred c) ≃ᵘ mkℚᵘ (+ n) (ℕ.pred d)
  /-injective-≃-helper {m} {n} {c} {d} -norm≡norm = contradiction
    (sym -norm≡norm)
    (nonNeg≢neg (normalize n d) (- normalize (suc m) c))
    where instance
      _ : NonNegative (normalize n d)
      _ = normalize-nonNeg n d

      _ : Negative (- normalize (suc m) c)
      _ = neg-pos {normalize (suc m) c} (normalize-pos (suc m) c)

/-injective-≃ : ∀ p q → ↥ᵘ p / ↧ₙᵘ p ≡ ↥ᵘ q / ↧ₙᵘ q → p ≃ᵘ q
/-injective-≃ (mkℚᵘ (+ m)    c-1) (mkℚᵘ (+ n)    d-1) eq =
  *≡* (cong (Sign.+ ◃_) (normalize-injective-≃ m n _ _ eq))
/-injective-≃ (mkℚᵘ (+ m)    c-1) (mkℚᵘ -[1+ n ] d-1) eq =
  ℚᵘ.≃-sym (/-injective-≃-helper (sym eq))
/-injective-≃ (mkℚᵘ -[1+ m ] c-1) (mkℚᵘ (+ n)    d-1) eq =
  /-injective-≃-helper eq
/-injective-≃ (mkℚᵘ -[1+ m ] c-1) (mkℚᵘ -[1+ n ] d-1) eq =
  *≡* (cong (Sign.- ◃_) (normalize-injective-≃ (suc m) (suc n) _ _ (neg-injective eq)))

------------------------------------------------------------------------
-- Properties of toℚ/fromℚ
------------------------------------------------------------------------

↥ᵘ-toℚᵘ : ∀ p → ↥ᵘ (toℚᵘ p) ≡ ↥ p
↥ᵘ-toℚᵘ p@record{} = refl

↧ᵘ-toℚᵘ : ∀ p → ↧ᵘ (toℚᵘ p) ≡ ↧ p
↧ᵘ-toℚᵘ p@record{} = refl

toℚᵘ-injective : Injective _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-injective {x@record{}} {y@record{}} (*≡* eq) = ≃⇒≡ (*≡* eq)

fromℚᵘ-injective : Injective _≃ᵘ_ _≡_ fromℚᵘ
fromℚᵘ-injective {p@record{}} {q@record{}} = /-injective-≃ p q

fromℚᵘ-toℚᵘ : ∀ p → fromℚᵘ (toℚᵘ p) ≡ p
fromℚᵘ-toℚᵘ (mkℚ (+ n)      d-1 c) = normalize-coprime c
fromℚᵘ-toℚᵘ (mkℚ (-[1+ n ]) d-1 c) = cong (-_) (normalize-coprime c)

toℚᵘ-fromℚᵘ : ∀ p → toℚᵘ (fromℚᵘ p) ≃ᵘ p
toℚᵘ-fromℚᵘ p = fromℚᵘ-injective (fromℚᵘ-toℚᵘ (fromℚᵘ p))

toℚᵘ-cong : Congruent _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-cong refl = *≡* refl

fromℚᵘ-cong : Congruent _≃ᵘ_ _≡_ fromℚᵘ
fromℚᵘ-cong {p} {q} p≃q = toℚᵘ-injective (begin-equality
  toℚᵘ (fromℚᵘ p)  ≃⟨  toℚᵘ-fromℚᵘ p ⟩
  p                ≃⟨  p≃q ⟩
  q                ≃⟨ toℚᵘ-fromℚᵘ q ⟨
  toℚᵘ (fromℚᵘ q)  ∎)
  where open ℚᵘ.≤-Reasoning

toℚᵘ-isRelHomomorphism : IsRelHomomorphism _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-isRelHomomorphism = record
  { cong = toℚᵘ-cong
  }

toℚᵘ-isRelMonomorphism : IsRelMonomorphism _≡_ _≃ᵘ_ toℚᵘ
toℚᵘ-isRelMonomorphism = record
  { isHomomorphism = toℚᵘ-isRelHomomorphism
  ; injective      = toℚᵘ-injective
  }

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

drop-*≤* : p ≤ q → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p)
drop-*≤* (*≤* pq≤qp) = pq≤qp

------------------------------------------------------------------------
-- toℚᵘ is a isomorphism

toℚᵘ-mono-≤ : p ≤ q → toℚᵘ p ≤ᵘ toℚᵘ q
toℚᵘ-mono-≤ {p@record{}} {q@record{}} (*≤* p≤q) = *≤* p≤q

toℚᵘ-cancel-≤ : toℚᵘ p ≤ᵘ toℚᵘ q → p ≤ q
toℚᵘ-cancel-≤ {p@record{}} {q@record{}} (*≤* p≤q) = *≤* p≤q

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
≤-antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (*≡* (ℤ.≤-antisym le₁ le₂))

≤-total : Total _≤_
≤-total p q = [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′ (ℤ.≤-total (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p))

infix 4 _≤?_ _≥?_

_≤?_ : Decidable _≤_
p ≤? q = Dec.map′ *≤* drop-*≤* (↥ p ℤ.* ↧ q ℤ.≤? ↥ q ℤ.* ↧ p)

_≥?_ : Decidable _≥_
_≥?_ = flip _≤?_

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

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
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
  ; _≈?_         = _≡?_
  ; _≤?_         = _≤?_
  }

------------------------------------------------------------------------
-- Bundles

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record
  { isTotalPreorder = ≤-isTotalPreorder
  }

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

drop-*<* : p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
drop-*<* (*<* pq<qp) = pq<qp

------------------------------------------------------------------------
-- toℚᵘ is a isomorphism

toℚᵘ-mono-< : p < q → toℚᵘ p <ᵘ toℚᵘ q
toℚᵘ-mono-< {p@record{}} {q@record{}} (*<* p<q) = *<* p<q

toℚᵘ-cancel-< : toℚᵘ p <ᵘ toℚᵘ q → p < q
toℚᵘ-cancel-< {p@record{}} {q@record{}} (*<* p<q) = *<* p<q

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

------------------------------------------------------------------------
-- Relational properties

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤ.<⇒≤ p<q)

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ p≮q = *≤* (ℤ.≮⇒≥ (p≮q ∘ *<*))

≰⇒> : _≰_ ⇒ _>_
≰⇒> p≰q = *<* (ℤ.≰⇒> (p≰q ∘ *≤*))

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (*<* p<q) = ℤ.<⇒≢ p<q ∘ drop-*≡* ∘ ≡⇒≃

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ (*≤* p≤q) (*<* q<p) = ℤ.≤⇒≯ p≤q q<p

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (*<* p<p) = ℤ.<-irrefl refl p<p

<-asym : Asymmetric _<_
<-asym (*<* p<q) (*<* q<p) = ℤ.<-asym p<q q<p

<-dense : Dense _<_
<-dense {p} {q} p<q = let
    m , p<ᵘm , m<ᵘq = ℚᵘ.<-dense (toℚᵘ-mono-< p<q)

    m≃m : m ≃ᵘ toℚᵘ (fromℚᵘ m)
    m≃m = ℚᵘ.≃-sym (toℚᵘ-fromℚᵘ m)

    p<m : p < fromℚᵘ m
    p<m = toℚᵘ-cancel-< (ℚᵘ.<-respʳ-≃ m≃m p<ᵘm)

    m<q : fromℚᵘ m < q
    m<q = toℚᵘ-cancel-< (ℚᵘ.<-respˡ-≃ m≃m m<ᵘq)
  in fromℚᵘ m , p<m , m<q

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {p} {q} {r} (*<* p<q) (*≤* q≤r) = *<*
  (ℤ.*-cancelʳ-<-nonNeg _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  ℤ.* sd₃) ℤ.* sd₂  ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁   ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm sd₃ sd₂) ⟩
  n₁   ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  ℤ.* sd₂) ℤ.* sd₃  <⟨ ℤ.*-monoʳ-<-pos (↧ r) p<q ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) ≤⟨ ℤ.*-monoˡ-≤-nonNeg (↧ p) q≤r ⟩
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
  (n₁  ℤ.* sd₂) ℤ.* sd₃  ≤⟨ ℤ.*-monoʳ-≤-nonNeg (↧ r) p≤q ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) <⟨ ℤ.*-monoˡ-<-pos (↧ p) q<r ⟩
  sd₁  ℤ.* (n₃  ℤ.* sd₂) ≡⟨ sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃)  ℤ.* sd₂  ≡⟨ cong (ℤ._* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃  ℤ.* sd₁) ℤ.* sd₂  ∎))
  where open ℤ.≤-Reasoning

<-trans : Transitive _<_
<-trans p<q = ≤-<-trans (<⇒≤ p<q)

infix 4 _<?_ _>?_

_<?_ : Decidable _<_
p <? q = Dec.map′ *<* drop-*<* ((↥ p ℤ.* ↧ q) ℤ.<? (↥ q ℤ.* ↧ p))

_>?_ : Decidable _>_
_>?_ = flip _<?_

<-cmp : Trichotomous _≡_ _<_
<-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ drop-*≡* ∘ ≡⇒≃) (≯ ∘ drop-*<*)
... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ (*≡* ≡))   (≯ ∘ drop-*<*)
... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ drop-*≡* ∘ ≡⇒≃) (*<* >)

<-irrelevant : Irrelevant _<_
<-irrelevant (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤ.<-irrelevant p<q₁ p<q₂)

<-respʳ-≡ : _<_ Respectsʳ _≡_
<-respʳ-≡ = subst (_ <_)

<-respˡ-≡ : _<_ Respectsˡ _≡_
<-respˡ-≡ = subst (_< _)

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = <-respˡ-≡ , <-respʳ-≡

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
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }

<-isDenseLinearOrder : IsDenseLinearOrder _≡_ _<_
<-isDenseLinearOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  ; dense              = <-dense
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

<-denseLinearOrder : DenseLinearOrder 0ℓ 0ℓ 0ℓ
<-denseLinearOrder = record
  { isDenseLinearOrder = <-isDenseLinearOrder
  }

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-asym
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    as Triple

  open Triple public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)

  ≃-go : Trans _≃_ _IsRelatedTo_ _IsRelatedTo_
  ≃-go = Triple.≈-go ∘′ ≃⇒≡

  open ≃-syntax _IsRelatedTo_ _IsRelatedTo_ ≃-go (λ {x y} → ≃-sym {x} {y}) public

------------------------------------------------------------------------
-- Properties of Positive/NonPositive/Negative/NonNegative and _≤_/_<_

positive⁻¹ : ∀ p → .{{Positive p}} → p > 0ℚ
positive⁻¹ p = toℚᵘ-cancel-< (ℚᵘ.positive⁻¹ (toℚᵘ p))

nonNegative⁻¹ : ∀ p → .{{NonNegative p}} → p ≥ 0ℚ
nonNegative⁻¹ p = toℚᵘ-cancel-≤ (ℚᵘ.nonNegative⁻¹ (toℚᵘ p))

negative⁻¹ : ∀ p → .{{Negative p}} → p < 0ℚ
negative⁻¹ p = toℚᵘ-cancel-< (ℚᵘ.negative⁻¹ (toℚᵘ p))

nonPositive⁻¹ : ∀ p → .{{NonPositive p}} → p ≤ 0ℚ
nonPositive⁻¹ p = toℚᵘ-cancel-≤ (ℚᵘ.nonPositive⁻¹ (toℚᵘ p))

neg<pos : ∀ p q → .{{Negative p}} → .{{Positive q}} → p < q
neg<pos p q = toℚᵘ-cancel-< (ℚᵘ.neg<pos (toℚᵘ p) (toℚᵘ q))

------------------------------------------------------------------------
-- Properties of -_ and _≤_/_<_

neg-antimono-< : -_ Preserves _<_ ⟶ _>_
neg-antimono-< {mkℚ -[1+ _ ] _ _} {mkℚ -[1+ _ ] _ _} (*<* (ℤ.-<- n<m)) = *<* (ℤ.+<+ (ℕ.s<s n<m))
neg-antimono-< {mkℚ -[1+ _ ] _ _} {mkℚ +0       _ _} (*<* ℤ.-<+)       = *<* (ℤ.+<+ ℕ.z<s)
neg-antimono-< {mkℚ -[1+ _ ] _ _} {mkℚ +[1+ _ ] _ _} (*<* ℤ.-<+)       = *<* ℤ.-<+
neg-antimono-< {mkℚ +0       _ _} {mkℚ +0       _ _} (*<* (ℤ.+<+ m<n)) = *<* (ℤ.+<+ m<n)
neg-antimono-< {mkℚ +0       _ _} {mkℚ +[1+ _ ] _ _} (*<* (ℤ.+<+ m<n)) = *<* ℤ.-<+
neg-antimono-< {mkℚ +[1+ _ ] _ _} {mkℚ +0       _ _} (*<* (ℤ.+<+ ()))
neg-antimono-< {mkℚ +[1+ _ ] _ _} {mkℚ +[1+ _ ] _ _} (*<* (ℤ.+<+ (ℕ.s<s m<n))) = *<* (ℤ.-<- m<n)

neg-antimono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-antimono-≤ {mkℚ -[1+ _ ] _ _} {mkℚ -[1+ _ ] _ _} (*≤* (ℤ.-≤- n≤m)) = *≤* (ℤ.+≤+ (ℕ.s≤s n≤m))
neg-antimono-≤ {mkℚ -[1+ _ ] _ _} {mkℚ +0       _ _} (*≤* ℤ.-≤+)       = *≤* (ℤ.+≤+ ℕ.z≤n)
neg-antimono-≤ {mkℚ -[1+ _ ] _ _} {mkℚ +[1+ _ ] _ _} (*≤* ℤ.-≤+)       = *≤* ℤ.-≤+
neg-antimono-≤ {mkℚ +0       _ _} {mkℚ +0       _ _} (*≤* (ℤ.+≤+ m≤n)) = *≤* (ℤ.+≤+ m≤n)
neg-antimono-≤ {mkℚ +0       _ _} {mkℚ +[1+ _ ] _ _} (*≤* (ℤ.+≤+ m≤n)) = *≤* ℤ.-≤+
neg-antimono-≤ {mkℚ +[1+ _ ] _ _} {mkℚ +0       _ _} (*≤* (ℤ.+≤+ ()))
neg-antimono-≤ {mkℚ +[1+ _ ] _ _} {mkℚ +[1+ _ ] _ _} (*≤* (ℤ.+≤+ (ℕ.s≤s m≤n))) = *≤* (ℤ.-≤- m≤n)

------------------------------------------------------------------------
-- Properties of _≤ᵇ_
------------------------------------------------------------------------

≤ᵇ⇒≤ : T (p ≤ᵇ q) → p ≤ q
≤ᵇ⇒≤ = *≤* ∘′ ℤ.≤ᵇ⇒≤

≤⇒≤ᵇ : p ≤ q → T (p ≤ᵇ q)
≤⇒≤ᵇ = ℤ.≤⇒≤ᵇ ∘′ drop-*≤*

------------------------------------------------------------------------
-- Properties of _<ᵇ_
------------------------------------------------------------------------

<ᵇ⇒< : T (p <ᵇ q) → p < q
<ᵇ⇒< = *<* ∘′ ℤ.<ᵇ⇒<

<⇒<ᵇ : p < q → T (p <ᵇ q)
<⇒<ᵇ = ℤ.<⇒<ᵇ ∘′ drop-*<*

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
↥-+ p@record{} q@record{} = ↥-/ (↥+ᵘ p q) (↧ₙ p ℕ.* ↧ₙ q)

↧-+ : ∀ p q → ↧ (p + q) ℤ.* +-nf p q ≡ ↧+ᵘ p q
↧-+ p@record{} q@record{} = ↧-/ (↥+ᵘ p q) (↧ₙ p ℕ.* ↧ₙ q)


------------------------------------------------------------------------
-- Monomorphic to unnormalised _+_

open Definitions ℚ ℚᵘ ℚᵘ._≃_

toℚᵘ-homo-+ : Homomorphic₂ toℚᵘ _+_ ℚᵘ._+_
toℚᵘ-homo-+ p@record{} q@record{} with +-nf p q ℤ.≡? 0ℤ
... | yes nf[p,q]≡0 = *≡* $ begin
  ↥ᵘ (toℚᵘ (p + q)) ℤ.* ↧+ᵘ p q   ≡⟨ cong (ℤ._* ↧+ᵘ p q) (↥ᵘ-toℚᵘ (p + q)) ⟩
  ↥ (p + q) ℤ.* ↧+ᵘ p q           ≡⟨ cong (ℤ._* ↧+ᵘ p q) eq ⟩
  0ℤ        ℤ.* ↧+ᵘ p q           ≡⟨⟩
  0ℤ        ℤ.* ↧ (p + q)         ≡⟨ cong (ℤ._* ↧ (p + q)) (sym eq2) ⟩
  ↥+ᵘ p q   ℤ.* ↧ (p + q)         ≡⟨ cong (↥+ᵘ p q ℤ.*_) (sym (↧ᵘ-toℚᵘ (p + q))) ⟩
  ↥+ᵘ p q   ℤ.* ↧ᵘ (toℚᵘ (p + q)) ∎
  where
  open ≡-Reasoning
  eq2 : ↥+ᵘ p q ≡ 0ℤ
  eq2 = gcd[i,j]≡0⇒i≡0 (↥+ᵘ p q) (↧+ᵘ p q) nf[p,q]≡0

  eq : ↥ (p + q) ≡ 0ℤ
  eq rewrite eq2 = cong ↥_ (0/n≡0 (↧ₙ p ℕ.* ↧ₙ q))

... | no  nf[p,q]≢0 = *≡* (ℤ.*-cancelʳ-≡ _ _ (+-nf p q) {{ℤ.≢-nonZero nf[p,q]≢0}} (begin
    (↥ᵘ (toℚᵘ (p + q))) ℤ.* ↧+ᵘ p q  ℤ.* +-nf p q ≡⟨ cong (λ v → v ℤ.* ↧+ᵘ p q ℤ.* +-nf p q) (↥ᵘ-toℚᵘ (p + q)) ⟩
    ↥ (p + q) ℤ.* ↧+ᵘ p q ℤ.* +-nf p q            ≡⟨ xy∙z≈xz∙y (↥ (p + q)) _ _ ⟩
    ↥ (p + q) ℤ.* +-nf p q ℤ.* ↧+ᵘ p q            ≡⟨ cong (ℤ._* ↧+ᵘ p q) (↥-+ p q) ⟩
    ↥+ᵘ p q ℤ.* ↧+ᵘ p q                           ≡⟨ cong (↥+ᵘ p q ℤ.*_) (sym (↧-+ p q)) ⟩
    ↥+ᵘ p q ℤ.* (↧ (p + q) ℤ.* +-nf p q)          ≡⟨ x∙yz≈xy∙z (↥+ᵘ p q) _ _ ⟩
    ↥+ᵘ p q ℤ.* ↧ (p + q)  ℤ.* +-nf p q           ≡⟨ cong (λ v → ↥+ᵘ p q ℤ.* v ℤ.* +-nf p q) (↧ᵘ-toℚᵘ (p + q)) ⟨
    ↥+ᵘ p q ℤ.* ↧ᵘ (toℚᵘ (p + q)) ℤ.* +-nf p q    ∎))
  where open ≡-Reasoning; open CommSemigroupProperties ℤ.*-commutativeSemigroup

toℚᵘ-isMagmaHomomorphism-+ : IsMagmaHomomorphism +-rawMagma ℚᵘ.+-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-+ = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; ∙-homo            = toℚᵘ-homo-+
  }

toℚᵘ-isMonoidHomomorphism-+ : IsMonoidHomomorphism +-0-rawMonoid ℚᵘ.+-0-rawMonoid toℚᵘ
toℚᵘ-isMonoidHomomorphism-+ = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-+
  ; ε-homo              = ℚᵘ.≃-refl
  }

toℚᵘ-isMonoidMonomorphism-+ : IsMonoidMonomorphism +-0-rawMonoid ℚᵘ.+-0-rawMonoid toℚᵘ
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

-‿cong : Congruent₁ (-_)
-‿cong = +-Monomorphism.⁻¹-cong ℚᵘ.+-isMagma ℚᵘ.-‿cong

neg-distrib-+ : ∀ p q → - (p + q) ≡ (- p) + (- q)
neg-distrib-+ = +-Monomorphism.⁻¹-distrib-∙ ℚᵘ.+-0-isAbelianGroup (ℚᵘ.≃-reflexive ∘₂ ℚᵘ.neg-distrib-+)

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
-- Properties of _+_ and _≤_

+-mono-≤ : Monotonic₂ _≤_ _≤_ _≤_ _+_
+-mono-≤ {p} {q} {r} {s} p≤q r≤s = toℚᵘ-cancel-≤ (begin
  toℚᵘ(p + r)          ≃⟨ toℚᵘ-homo-+ p r ⟩
  toℚᵘ(p) ℚᵘ.+ toℚᵘ(r) ≤⟨ ℚᵘ.+-mono-≤ (toℚᵘ-mono-≤ p≤q) (toℚᵘ-mono-≤ r≤s) ⟩
  toℚᵘ(q) ℚᵘ.+ toℚᵘ(s) ≃⟨ ℚᵘ.≃-sym (toℚᵘ-homo-+ q s) ⟩
  toℚᵘ(q + s)          ∎)
  where open ℚᵘ.≤-Reasoning

+-monoˡ-≤ : RightMonotonic _≤_ _≤_ _+_
+-monoˡ-≤ r p≤q = +-mono-≤ p≤q (≤-refl {r})

+-monoʳ-≤ : LeftMonotonic _≤_ _≤_ _+_
+-monoʳ-≤ r p≤q = +-mono-≤ (≤-refl {r}) p≤q

nonNeg+nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} q .{{_ : NonNegative q}} → NonNegative (p + q)
nonNeg+nonNeg⇒nonNeg p q = nonNegative $ +-mono-≤ (nonNegative⁻¹ p) (nonNegative⁻¹ q)

nonPos+nonPos⇒nonPos : ∀ p .{{_ : NonPositive p}} q .{{_ : NonPositive q}} → NonPositive (p + q)
nonPos+nonPos⇒nonPos p q = nonPositive $ +-mono-≤ (nonPositive⁻¹ p) (nonPositive⁻¹ q)

------------------------------------------------------------------------
-- Properties of _+_ and _<_

+-mono-<-≤ : Monotonic₂ _<_ _≤_ _<_ _+_
+-mono-<-≤ {p} {q} {r} {s} p<q r≤s = toℚᵘ-cancel-< (begin-strict
  toℚᵘ(p + r)          ≃⟨ toℚᵘ-homo-+ p r ⟩
  toℚᵘ(p) ℚᵘ.+ toℚᵘ(r) <⟨ ℚᵘ.+-mono-<-≤ (toℚᵘ-mono-< p<q) (toℚᵘ-mono-≤ r≤s) ⟩
  toℚᵘ(q) ℚᵘ.+ toℚᵘ(s) ≃⟨ ℚᵘ.≃-sym (toℚᵘ-homo-+ q s) ⟩
  toℚᵘ(q + s)          ∎)
  where open ℚᵘ.≤-Reasoning

+-mono-≤-< : Monotonic₂ _≤_ _<_ _<_ _+_
+-mono-≤-< {p} {q} {r} {s} p≤q r<s rewrite +-comm p r | +-comm q s = +-mono-<-≤ r<s p≤q

+-mono-< : Monotonic₂ _<_ _<_ _<_ _+_
+-mono-< {p} {q} {r} {s} p<q r<s = <-trans (+-mono-<-≤ p<q (≤-refl {r})) (+-mono-≤-< (≤-refl {q}) r<s)

+-monoˡ-< : RightMonotonic _<_ _<_ _+_
+-monoˡ-< r p<q = +-mono-<-≤ p<q (≤-refl {r})

+-monoʳ-< : LeftMonotonic _<_ _<_ _+_
+-monoʳ-< r p<q = +-mono-≤-< (≤-refl {r}) p<q

pos+nonNeg⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : NonNegative q}} → Positive (p + q)
pos+nonNeg⇒pos p q = positive $ +-mono-<-≤ (positive⁻¹ p) (nonNegative⁻¹ q)

nonNeg+pos⇒pos : ∀ p .{{_ : NonNegative p}} q .{{_ : Positive q}} → Positive (p + q)
nonNeg+pos⇒pos p q = positive $ +-mono-≤-< (nonNegative⁻¹ p) (positive⁻¹ q)

pos+pos⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : Positive q}} → Positive (p + q)
pos+pos⇒pos p q = positive $ +-mono-< (positive⁻¹ p) (positive⁻¹ q)

neg+nonPos⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : NonPositive q}} → Negative (p + q)
neg+nonPos⇒neg p q = negative $ +-mono-<-≤ (negative⁻¹ p) (nonPositive⁻¹ q)

nonPos+neg⇒neg : ∀ p .{{_ : NonPositive p}} q .{{_ : Negative q}} → Negative (p + q)
nonPos+neg⇒neg p q = negative $ +-mono-≤-< (nonPositive⁻¹ p) (negative⁻¹ q)

neg+neg⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : Negative q}} → Negative (p + q)
neg+neg⇒neg p q = negative $ +-mono-< (negative⁻¹ p) (negative⁻¹ q)

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

private
  *-nf : ℚ → ℚ → ℤ
  *-nf p q = gcd (↥ p ℤ.* ↥ q) (↧ p ℤ.* ↧ q)

↥-* : ∀ p q → ↥ (p * q) ℤ.* *-nf p q ≡ ↥ p ℤ.* ↥ q
↥-* p@record{} q@record{} = ↥-/ (↥ p ℤ.* ↥ q) (↧ₙ p ℕ.* ↧ₙ q)

↧-* : ∀ p q → ↧ (p * q) ℤ.* *-nf p q ≡ ↧ p ℤ.* ↧ q
↧-* p@record{} q@record{} = ↧-/ (↥ p ℤ.* ↥ q) (↧ₙ p ℕ.* ↧ₙ q)

------------------------------------------------------------------------
-- Monomorphic to unnormalised _*_

toℚᵘ-homo-* : Homomorphic₂ toℚᵘ _*_ ℚᵘ._*_
toℚᵘ-homo-* p@record{} q@record{} with *-nf p q ℤ.≡? 0ℤ
... | yes nf[p,q]≡0 = *≡* $ begin
  ↥ᵘ (toℚᵘ (p * q)) ℤ.* (↧ p ℤ.* ↧ q)     ≡⟨ cong (ℤ._* (↧ p ℤ.* ↧ q)) (↥ᵘ-toℚᵘ (p * q)) ⟩
  ↥ (p * q)         ℤ.* (↧ p ℤ.* ↧ q)     ≡⟨ cong (ℤ._* (↧ p ℤ.* ↧ q)) eq ⟩
  0ℤ                ℤ.* (↧ p ℤ.* ↧ q)     ≡⟨⟩
  0ℤ                ℤ.* ↧ (p * q)         ≡⟨ cong (ℤ._* ↧ (p * q)) (sym eq2) ⟩
  (↥ p ℤ.* ↥ q)     ℤ.* ↧ (p * q)         ≡⟨ cong ((↥ p ℤ.* ↥ q) ℤ.*_) (sym (↧ᵘ-toℚᵘ (p * q))) ⟩
  (↥ p ℤ.* ↥ q)     ℤ.* ↧ᵘ (toℚᵘ (p * q)) ∎
  where
  open ≡-Reasoning
  eq2 : ↥ p ℤ.* ↥ q ≡ 0ℤ
  eq2 = gcd[i,j]≡0⇒i≡0 (↥ p ℤ.* ↥ q) (↧ p ℤ.* ↧ q) nf[p,q]≡0

  eq : ↥ (p * q) ≡ 0ℤ
  eq rewrite eq2 = cong ↥_ (0/n≡0 (↧ₙ p ℕ.* ↧ₙ q))
... | no nf[p,q]≢0 = *≡* (ℤ.*-cancelʳ-≡ _ _ (*-nf p q) {{ℤ.≢-nonZero nf[p,q]≢0}} (begin
  ↥ᵘ (toℚᵘ (p * q)) ℤ.* (↧ p ℤ.* ↧ q) ℤ.* *-nf p q     ≡⟨ cong (λ v → v ℤ.* (↧ p ℤ.* ↧ q) ℤ.* *-nf p q) (↥ᵘ-toℚᵘ (p * q)) ⟩
  ↥ (p * q)         ℤ.* (↧ p ℤ.* ↧ q) ℤ.* *-nf p q     ≡⟨ xy∙z≈xz∙y (↥ (p * q)) _ _ ⟩
  ↥ (p * q)         ℤ.* *-nf p q ℤ.* (↧ p ℤ.* ↧ q)     ≡⟨ cong (ℤ._* (↧ p ℤ.* ↧ q)) (↥-* p q) ⟩
  (↥ p ℤ.* ↥ q)     ℤ.* (↧ p ℤ.* ↧ q)                  ≡⟨ cong ((↥ p ℤ.* ↥ q) ℤ.*_) (sym (↧-* p q)) ⟩
  (↥ p ℤ.* ↥ q)     ℤ.* (↧ (p * q) ℤ.* *-nf p q)       ≡⟨ x∙yz≈xy∙z (↥ p ℤ.* ↥ q) _ _ ⟩
  (↥ p ℤ.* ↥ q)     ℤ.* ↧ (p * q)  ℤ.* *-nf p q        ≡⟨ cong (λ v → (↥ p ℤ.* ↥ q) ℤ.* v ℤ.* *-nf p q) (↧ᵘ-toℚᵘ (p * q)) ⟨
  (↥ p ℤ.* ↥ q)     ℤ.* ↧ᵘ (toℚᵘ (p * q)) ℤ.* *-nf p q ∎))
  where open ≡-Reasoning; open CommSemigroupProperties ℤ.*-commutativeSemigroup

toℚᵘ-homo-1/ : ∀ p .{{_ : NonZero p}} → toℚᵘ (1/ p) ℚᵘ.≃ (ℚᵘ.1/ toℚᵘ p)
toℚᵘ-homo-1/ (mkℚ +[1+ _ ] _ _) = ℚᵘ.≃-refl
toℚᵘ-homo-1/ (mkℚ -[1+ _ ] _ _) = ℚᵘ.≃-refl

toℚᵘ-isMagmaHomomorphism-* : IsMagmaHomomorphism *-rawMagma ℚᵘ.*-rawMagma toℚᵘ
toℚᵘ-isMagmaHomomorphism-* = record
  { isRelHomomorphism = toℚᵘ-isRelHomomorphism
  ; ∙-homo              = toℚᵘ-homo-*
  }

toℚᵘ-isMonoidHomomorphism-* : IsMonoidHomomorphism *-1-rawMonoid ℚᵘ.*-1-rawMonoid toℚᵘ
toℚᵘ-isMonoidHomomorphism-* = record
  { isMagmaHomomorphism = toℚᵘ-isMagmaHomomorphism-*
  ; ε-homo              = ℚᵘ.≃-refl
  }

toℚᵘ-isMonoidMonomorphism-* : IsMonoidMonomorphism *-1-rawMonoid ℚᵘ.*-1-rawMonoid toℚᵘ
toℚᵘ-isMonoidMonomorphism-* = record
  { isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-*
  ; injective            = toℚᵘ-injective
  }

toℚᵘ-isNearSemiringHomomorphism-+-* : IsNearSemiringHomomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
toℚᵘ-isNearSemiringHomomorphism-+-* = record
  { +-isMonoidHomomorphism = toℚᵘ-isMonoidHomomorphism-+
  ; *-homo                 = toℚᵘ-homo-*
  }

toℚᵘ-isNearSemiringMonomorphism-+-* : IsNearSemiringMonomorphism +-*-rawNearSemiring ℚᵘ.+-*-rawNearSemiring toℚᵘ
toℚᵘ-isNearSemiringMonomorphism-+-* = record
  { isNearSemiringHomomorphism = toℚᵘ-isNearSemiringHomomorphism-+-*
  ; injective                  = toℚᵘ-injective
  }

toℚᵘ-isSemiringHomomorphism-+-* : IsSemiringHomomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
toℚᵘ-isSemiringHomomorphism-+-* = record
  { isNearSemiringHomomorphism = toℚᵘ-isNearSemiringHomomorphism-+-*
  ; 1#-homo                    = ℚᵘ.≃-refl
  }

toℚᵘ-isSemiringMonomorphism-+-* : IsSemiringMonomorphism +-*-rawSemiring ℚᵘ.+-*-rawSemiring toℚᵘ
toℚᵘ-isSemiringMonomorphism-+-* = record
  { isSemiringHomomorphism = toℚᵘ-isSemiringHomomorphism-+-*
  ; injective              = toℚᵘ-injective
  }

toℚᵘ-isRingHomomorphism-+-* : IsRingHomomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ
toℚᵘ-isRingHomomorphism-+-* = record
  { isSemiringHomomorphism = toℚᵘ-isSemiringHomomorphism-+-*
  ; -‿homo                 = toℚᵘ-homo‿-
  }

toℚᵘ-isRingMonomorphism-+-* : IsRingMonomorphism +-*-rawRing ℚᵘ.+-*-rawRing toℚᵘ
toℚᵘ-isRingMonomorphism-+-* = record
  { isRingHomomorphism = toℚᵘ-isRingHomomorphism-+-*
  ; injective          = toℚᵘ-injective
  }

------------------------------------------------------------------------
-- Algebraic properties

private
  module +-*-Monomorphism = RingMonomorphisms toℚᵘ-isRingMonomorphism-+-*

*-assoc : Associative _*_
*-assoc = +-*-Monomorphism.*-assoc ℚᵘ.*-isMagma ℚᵘ.*-assoc

*-comm : Commutative _*_
*-comm = +-*-Monomorphism.*-comm ℚᵘ.*-isMagma ℚᵘ.*-comm

*-identityˡ : LeftIdentity 1ℚ _*_
*-identityˡ = +-*-Monomorphism.*-identityˡ ℚᵘ.*-isMagma ℚᵘ.*-identityˡ

*-identityʳ : RightIdentity 1ℚ _*_
*-identityʳ = +-*-Monomorphism.*-identityʳ ℚᵘ.*-isMagma ℚᵘ.*-identityʳ

*-identity : Identity 1ℚ _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero 0ℚ _*_
*-zeroˡ = +-*-Monomorphism.zeroˡ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-zeroˡ

*-zeroʳ : RightZero 0ℚ _*_
*-zeroʳ = +-*-Monomorphism.zeroʳ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-zeroʳ

*-zero : Zero 0ℚ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = +-*-Monomorphism.distribˡ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribˡ-+

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = +-*-Monomorphism.distribʳ ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.*-distribʳ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-inverseˡ : ∀ p .{{_ : NonZero p}} → (1/ p) * p ≡ 1ℚ
*-inverseˡ p = toℚᵘ-injective (begin-equality
  toℚᵘ (1/ p * p)             ≃⟨ toℚᵘ-homo-* (1/ p) p ⟩
  toℚᵘ (1/ p) ℚᵘ.* toℚᵘ p     ≃⟨ ℚᵘ.*-congʳ (toℚᵘ-homo-1/ p) ⟩
  ℚᵘ.1/ (toℚᵘ p) ℚᵘ.* toℚᵘ p  ≃⟨ ℚᵘ.*-inverseˡ (toℚᵘ p) ⟩
  ℚᵘ.1ℚᵘ                      ∎)
  where open ℚᵘ.≤-Reasoning

*-inverseʳ : ∀ p .{{_ : NonZero p}} → p * (1/ p) ≡ 1ℚ
*-inverseʳ p = trans (*-comm p (1/ p)) (*-inverseˡ p)

neg-distribˡ-* : ∀ p q → - (p * q) ≡ - p * q
neg-distribˡ-* = +-*-Monomorphism.neg-distribˡ-* ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.neg-distribˡ-*

neg-distribʳ-* : ∀ p q → - (p * q) ≡ p * - q
neg-distribʳ-* = +-*-Monomorphism.neg-distribʳ-* ℚᵘ.+-0-isGroup ℚᵘ.*-isMagma ℚᵘ.neg-distribʳ-*

p*q≡0⇒p≡0∨q≡0 : p * q ≡ 0ℚ → p ≡ 0ℚ ⊎ q ≡ 0ℚ
p*q≡0⇒p≡0∨q≡0 {p} {q} p*q≡0 =
  Sum.map toℚᵘ-injective toℚᵘ-injective $ ℚᵘ.p*q≃0⇒p≃0∨q≃0 $ begin-equality
    toℚᵘ p ℚᵘ.* toℚᵘ q ≃⟨ toℚᵘ-homo-* p q ⟨
    toℚᵘ (p * q)       ≡⟨ cong toℚᵘ p*q≡0 ⟩
    ℚᵘ.0ℚᵘ             ∎
  where open ℚᵘ.≤-Reasoning

p*q≢0⇒p≢0 : p * q ≢ 0ℚ → p ≢ 0ℚ
p*q≢0⇒p≢0 {p} {q} pq≢0 p≡0 = pq≢0 $ begin
  p * q  ≡⟨ cong (_* q) p≡0 ⟩
  0ℚ * q ≡⟨ *-zeroˡ q ⟩
  0ℚ     ∎
  where open ≡-Reasoning

p*q≢0⇒q≢0 : p * q ≢ 0ℚ → q ≢ 0ℚ
p*q≢0⇒q≢0 {p} {q} pq≢0 q≡0 = pq≢0 $ begin
  p * q  ≡⟨ cong (p *_) q≡0 ⟩
  p * 0ℚ ≡⟨ *-zeroʳ p ⟩
  0ℚ     ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Structures

*-isMagma : IsMagma _*_
*-isMagma = +-*-Monomorphism.*-isMagma ℚᵘ.*-isMagma

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = +-*-Monomorphism.*-isSemigroup ℚᵘ.*-isSemigroup

*-1-isMonoid : IsMonoid _*_ 1ℚ
*-1-isMonoid = +-*-Monomorphism.*-isMonoid ℚᵘ.*-1-isMonoid

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℚ
*-1-isCommutativeMonoid = +-*-Monomorphism.*-isCommutativeMonoid ℚᵘ.*-1-isCommutativeMonoid

+-*-isRing : IsRing _+_ _*_ -_ 0ℚ 1ℚ
+-*-isRing = +-*-Monomorphism.isRing ℚᵘ.+-*-isRing

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℚ 1ℚ
+-*-isCommutativeRing = +-*-Monomorphism.isCommutativeRing ℚᵘ.+-*-isCommutativeRing

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
-- HeytingField structures and bundles

module _ where
  open CommutativeRing +-*-commutativeRing
    using (+-group; zeroˡ; *-congʳ; isCommutativeRing)

  open GroupProperties +-group
  open DecSetoidProperties ≡-decSetoid

  #⇒invertible : p ≢ q → Invertible 1ℚ _*_ (p - q)
  #⇒invertible {p} {q} p≢q = let r = p - q in 1/ r , *-inverseˡ r , *-inverseʳ r
    where instance _ = ≢-nonZero (p≢q ∘ (x∙y⁻¹≈ε⇒x≈y p q))

  invertible⇒# : Invertible 1ℚ _*_ (p - q) → p ≢ q
  invertible⇒# {p} {q} (1/[p-q] , _ , [p-q]/[p-q]≡1) p≡q = contradiction 1≡0 1≢0
    where
    open ≈-Reasoning ≡-setoid
    1≡0 : 1ℚ ≡ 0ℚ
    1≡0 = begin
      1ℚ                 ≈⟨ [p-q]/[p-q]≡1 ⟨
      (p - q) * 1/[p-q]  ≈⟨ *-congʳ (x≈y⇒x∙y⁻¹≈ε p≡q) ⟩
      0ℚ * 1/[p-q]       ≈⟨ zeroˡ 1/[p-q] ⟩
      0ℚ                 ∎

  isHeytingCommutativeRing : IsHeytingCommutativeRing _≡_ _≢_ _+_ _*_ -_ 0ℚ 1ℚ
  isHeytingCommutativeRing = record
    { isCommutativeRing = isCommutativeRing
    ; isApartnessRelation = ≉-isApartnessRelation
    ; #⇒invertible = #⇒invertible
    ; invertible⇒# = invertible⇒#
    }

  isHeytingField : IsHeytingField _≡_ _≢_ _+_ _*_ -_ 0ℚ 1ℚ
  isHeytingField = record
    { isHeytingCommutativeRing = isHeytingCommutativeRing
    ; tight = ≉-tight
    }

  heytingCommutativeRing : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
  heytingCommutativeRing = record { isHeytingCommutativeRing = isHeytingCommutativeRing }

  heytingField : HeytingField 0ℓ 0ℓ 0ℓ
  heytingField = record { isHeytingField = isHeytingField }

------------------------------------------------------------------------
-- Properties of _*_ and _/_

*-cancelˡ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (p ℕ.* r)}} →
              (+ p ℤ.* q) / (p ℕ.* r) ≡ q / r
*-cancelˡ-/ p {q} {r} = proof q
  where
  open ≡-Reasoning

  *-cancelˡ-/-helper : ∀ qₙ → normalize (p ℕ.* qₙ) (p ℕ.* r) ≡ + qₙ / r
  *-cancelˡ-/-helper qₙ = mkℚ+-cong (lemma qₙ) (lemma r)
    where
    instance
      p≢0    = ℕ.m*n≢0⇒m≢0 p
      g≢0    = ℕ.≢-nonZero $ ℕ.gcd[m,n]≢0 (p ℕ.* qₙ) (p ℕ.* r) $ inj₂
                           $ ℕ.≢-nonZero⁻¹ $ p ℕ.* r
      n/g≢0  = ℕ.≢-nonZero $ ℕ.n/gcd[m,n]≢0 (p ℕ.* qₙ) (p ℕ.* r) {{gcd≢0 = g≢0}}
      g≢0'   = ℕ.≢-nonZero $ ℕ.gcd[m,n]≢0 qₙ r $ inj₂ $ ℕ.≢-nonZero⁻¹ r
      n/g≢0' = ℕ.≢-nonZero $ ℕ.n/gcd[m,n]≢0 qₙ r {{gcd≢0 = g≢0'}}
      p*g≢0  = ℕ.m*n≢0 p (ℕ.gcd qₙ r)

    lemma : ∀ n → (p ℕ.* n) ℕ./ ℕ.gcd (p ℕ.* qₙ) (p ℕ.* r) ≡ n ℕ./ ℕ.gcd qₙ r
    lemma n = begin
      p ℕ.* n ℕ./ ℕ.gcd (p ℕ.* qₙ) (p ℕ.* r)
        ≡⟨ ℕ./-congʳ $ ℕ.c*gcd[m,n]≡gcd[cm,cn] p qₙ r ⟨
      p ℕ.* n ℕ./ (p ℕ.* ℕ.gcd qₙ r)
        ≡⟨ ℕ.m*n/m*o≡n/o p n $ ℕ.gcd qₙ r ⟩
      n ℕ./ ℕ.gcd qₙ r
        ∎

  proof : ∀ q → (+ p ℤ.* q) / (p ℕ.* r) ≡ q / r
  proof (+ qₙ) = begin
    + p ℤ.* + qₙ / (p ℕ.* r) ≡⟨ /-cong (ℤ.pos-* p qₙ) refl ⟨
    + (p ℕ.* qₙ) / (p ℕ.* r) ≡⟨ *-cancelˡ-/-helper qₙ ⟩
    + qₙ / r                 ∎
  proof -[1+ qₙ ] = begin
    + p ℤ.* -[1+ qₙ ] / (p ℕ.* r)
      ≡⟨ /-cong (ℤ.neg-distribʳ-* (+ p) +[1+ qₙ ]) refl ⟨
    ℤ.- (Sign.+ ℤ.◃ p ℕ.* suc qₙ) / (p ℕ.* r)
      ≡⟨ /-cong (cong (ℤ.-_) (ℤ.pos-* p (suc qₙ))) refl ⟨
    ℤ.- + (p ℕ.* suc qₙ) / (p ℕ.* r)
      ≡⟨ -i/n≡-[i/n] (+ (p ℕ.* suc qₙ)) (p ℕ.* r) ⟩
    - (+ (p ℕ.* suc qₙ) / (p ℕ.* r))
      ≡⟨ cong (-_) $ *-cancelˡ-/-helper $ suc qₙ ⟩
    -[1+ qₙ ] / r
      ∎

*-cancelʳ-/ : ∀ p {q r} .{{_ : ℕ.NonZero r}} .{{_ : ℕ.NonZero (r ℕ.* p)}} →
              (q ℤ.* + p) / (r ℕ.* p) ≡ q / r
*-cancelʳ-/ p {q} {r} = begin
   q ℤ.* + p / (r ℕ.* p) ≡⟨ /-cong {q ℤ.* + p} refl (ℕ.*-comm r p) ⟩
   q ℤ.* + p / (p ℕ.* r) ≡⟨ /-cong (ℤ.*-comm q (+ p)) refl ⟩
   + p ℤ.* q / (p ℕ.* r) ≡⟨ *-cancelˡ-/ p ⟩
   q / r                 ∎
   where
   open ≡-Reasoning
   instance
     p≢0 : ℕ.NonZero p
     p≢0 = ℕ.m*n≢0⇒n≢0 r
     p*r≢0 : ℕ.NonZero (p ℕ.* r)
     p*r≢0 = ℕ.m*n≢0 p r

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-cancelʳ-≤-pos : ∀ r .{{_ : Positive r}} → p * r ≤ q * r → p ≤ q
*-cancelʳ-≤-pos {p} {q} r pr≤qr = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelʳ-≤-pos (toℚᵘ r) (begin
  toℚᵘ p ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* p r ⟨
  toℚᵘ (p * r)        ≤⟨  toℚᵘ-mono-≤ pr≤qr ⟩
  toℚᵘ (q * r)        ≃⟨  toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  ∎))
  where open ℚᵘ.≤-Reasoning

*-cancelˡ-≤-pos : ∀ r .{{_ : Positive r}} → r * p ≤ r * q → p ≤ q
*-cancelˡ-≤-pos {p} {q} r rewrite *-comm r p | *-comm r q = *-cancelʳ-≤-pos r

*-monoʳ-≤-nonNeg : ∀ r .{{_ : NonNegative r}} → Monotonic₁ _≤_ _≤_ (_* r)
*-monoʳ-≤-nonNeg r {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (p * r)        ≃⟨  toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r  ≤⟨  ℚᵘ.*-monoˡ-≤-nonNeg (toℚᵘ r) (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* q r ⟨
  toℚᵘ (q * r)        ∎)
  where open ℚᵘ.≤-Reasoning

*-monoˡ-≤-nonNeg : ∀ r .{{_ : NonNegative r}} → Monotonic₁ _≤_ _≤_ (r *_)
*-monoˡ-≤-nonNeg r {p} {q} rewrite *-comm r p | *-comm r q = *-monoʳ-≤-nonNeg r

*-monoʳ-≤-nonPos : ∀ r .{{_ : NonPositive r}} → Monotonic₁ _≤_ _≥_ (_* r)
*-monoʳ-≤-nonPos r {p} {q} p≤q = toℚᵘ-cancel-≤ (begin
  toℚᵘ (q * r)        ≃⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  ≤⟨ ℚᵘ.*-monoˡ-≤-nonPos (toℚᵘ r) (toℚᵘ-mono-≤ p≤q) ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* p r ⟨
  toℚᵘ (p * r)        ∎)
  where open ℚᵘ.≤-Reasoning

*-monoˡ-≤-nonPos : ∀ r .{{_ : NonPositive r}} → Monotonic₁ _≤_ _≥_ (r *_)
*-monoˡ-≤-nonPos r {p} {q} rewrite *-comm r p | *-comm r q = *-monoʳ-≤-nonPos r

*-cancelʳ-≤-neg : ∀ r .{{_ : Negative r}} → p * r ≤ q * r → p ≥ q
*-cancelʳ-≤-neg {p} {q} r pr≤qr = toℚᵘ-cancel-≤ (ℚᵘ.*-cancelʳ-≤-neg _ (begin
  toℚᵘ p ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* p r ⟨
  toℚᵘ (p * r)        ≤⟨ toℚᵘ-mono-≤ pr≤qr ⟩
  toℚᵘ (q * r)        ≃⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  ∎))
  where open ℚᵘ.≤-Reasoning

*-cancelˡ-≤-neg : ∀ r .{{_ : Negative r}} → r * p ≤ r * q → p ≥ q
*-cancelˡ-≤-neg {p} {q} r rewrite *-comm r p | *-comm r q = *-cancelʳ-≤-neg r

nonNeg*nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} q .{{_ : NonNegative q}} → NonNegative (p * q)
nonNeg*nonNeg⇒nonNeg p q = nonNegative $ begin
  0ℚ     ≡⟨ *-zeroʳ p ⟨
  p * 0ℚ ≤⟨ *-monoˡ-≤-nonNeg p (nonNegative⁻¹ q) ⟩
  p * q  ∎
  where open ≤-Reasoning

nonPos*nonNeg⇒nonPos : ∀ p .{{_ : NonPositive p}} q .{{_ : NonNegative q}} → NonPositive (p * q)
nonPos*nonNeg⇒nonPos p q = nonPositive $ begin
  p * q  ≤⟨ *-monoˡ-≤-nonPos p (nonNegative⁻¹ q) ⟩
  p * 0ℚ ≡⟨ *-zeroʳ p ⟩
  0ℚ     ∎
  where open ≤-Reasoning

nonNeg*nonPos⇒nonPos : ∀ p .{{_ : NonNegative p}} q .{{_ : NonPositive q}} → NonPositive (p * q)
nonNeg*nonPos⇒nonPos p q = nonPositive $ begin
  p * q  ≤⟨ *-monoˡ-≤-nonNeg p (nonPositive⁻¹ q) ⟩
  p * 0ℚ ≡⟨ *-zeroʳ p ⟩
  0ℚ     ∎
  where open ≤-Reasoning

nonPos*nonPos⇒nonNeg : ∀ p .{{_ : NonPositive p}} q .{{_ : NonPositive q}} → NonNegative (p * q)
nonPos*nonPos⇒nonNeg p q = nonNegative $ begin
  0ℚ     ≡⟨ *-zeroʳ p ⟨
  p * 0ℚ ≤⟨ *-monoˡ-≤-nonPos p (nonPositive⁻¹ q) ⟩
  p * q  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ r .{{_ : Positive r}} → Monotonic₁ _<_ _<_ (_* r)
*-monoˡ-<-pos r {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (p * r)        ≃⟨ toℚᵘ-homo-* p r ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r  <⟨ ℚᵘ.*-monoˡ-<-pos (toℚᵘ r) (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* q r ⟨
  toℚᵘ (q * r)        ∎)
  where open ℚᵘ.≤-Reasoning

*-monoʳ-<-pos : ∀ r .{{_ : Positive r}} → Monotonic₁ _<_ _<_ (r *_)
*-monoʳ-<-pos r {p} {q} rewrite *-comm r p | *-comm r q = *-monoˡ-<-pos r

*-cancelˡ-<-nonNeg : ∀ r .{{_ : NonNegative r}} → ∀ {p q} → r * p < r * q → p < q
*-cancelˡ-<-nonNeg r {p} {q} rp<rq = toℚᵘ-cancel-< (ℚᵘ.*-cancelˡ-<-nonNeg (toℚᵘ r) (begin-strict
  toℚᵘ r ℚᵘ.* toℚᵘ p  ≃⟨ toℚᵘ-homo-* r p ⟨
  toℚᵘ (r * p)        <⟨ toℚᵘ-mono-< rp<rq ⟩
  toℚᵘ (r * q)        ≃⟨ toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q  ∎))
  where open ℚᵘ.≤-Reasoning

*-cancelʳ-<-nonNeg : ∀ r .{{_ : NonNegative r}} → ∀ {p q} → p * r < q * r → p < q
*-cancelʳ-<-nonNeg r {p} {q} rewrite *-comm p r | *-comm q r = *-cancelˡ-<-nonNeg r

*-monoˡ-<-neg : ∀ r .{{_ : Negative r}} → Monotonic₁ _<_ _>_ (_* r)
*-monoˡ-<-neg r {p} {q} p<q = toℚᵘ-cancel-< (begin-strict
  toℚᵘ (q * r)        ≃⟨ toℚᵘ-homo-* q r ⟩
  toℚᵘ q ℚᵘ.* toℚᵘ r  <⟨ ℚᵘ.*-monoˡ-<-neg (toℚᵘ r) (toℚᵘ-mono-< p<q) ⟩
  toℚᵘ p ℚᵘ.* toℚᵘ r  ≃⟨ toℚᵘ-homo-* p r ⟨
  toℚᵘ (p * r)        ∎)
  where open ℚᵘ.≤-Reasoning

*-monoʳ-<-neg : ∀ r .{{_ : Negative r}} → Monotonic₁ _<_ _>_ (r *_)
*-monoʳ-<-neg r {p} {q} rewrite *-comm r p | *-comm r q = *-monoˡ-<-neg r

*-cancelˡ-<-nonPos : ∀ r .{{_ : NonPositive r}} → r * p < r * q → p > q
*-cancelˡ-<-nonPos {p} {q} r rp<rq = toℚᵘ-cancel-< (ℚᵘ.*-cancelˡ-<-nonPos (toℚᵘ r) (begin-strict
  toℚᵘ r ℚᵘ.* toℚᵘ p  ≃⟨ toℚᵘ-homo-* r p ⟨
  toℚᵘ (r * p)        <⟨  toℚᵘ-mono-< rp<rq ⟩
  toℚᵘ (r * q)        ≃⟨  toℚᵘ-homo-* r q ⟩
  toℚᵘ r ℚᵘ.* toℚᵘ q  ∎))
  where open ℚᵘ.≤-Reasoning

*-cancelʳ-<-nonPos : ∀ r .{{_ : NonPositive r}} → p * r < q * r → p > q
*-cancelʳ-<-nonPos {p} {q} r rewrite *-comm p r | *-comm q r = *-cancelˡ-<-nonPos r

pos*pos⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : Positive q}} → Positive (p * q)
pos*pos⇒pos p q = positive $ begin-strict
  0ℚ     ≡⟨ *-zeroʳ p ⟨
  p * 0ℚ <⟨ *-monoʳ-<-pos p (positive⁻¹ q) ⟩
  p * q  ∎
  where open ≤-Reasoning

neg*pos⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : Positive q}} → Negative (p * q)
neg*pos⇒neg p q = negative $ begin-strict
  p * q  <⟨ *-monoʳ-<-neg p (positive⁻¹ q) ⟩
  p * 0ℚ ≡⟨ *-zeroʳ p ⟩
  0ℚ     ∎
  where open ≤-Reasoning

pos*neg⇒neg : ∀ p .{{_ : Positive p}} q .{{_ : Negative q}} → Negative (p * q)
pos*neg⇒neg p q = negative $ begin-strict
  p * q  <⟨ *-monoʳ-<-pos p (negative⁻¹ q) ⟩
  p * 0ℚ ≡⟨ *-zeroʳ p ⟩
  0ℚ     ∎
  where open ≤-Reasoning

neg*neg⇒pos : ∀ p .{{_ : Negative p}} q .{{_ : Negative q}} → Positive (p * q)
neg*neg⇒pos p q = positive $ begin-strict
  0ℚ     ≡⟨ *-zeroʳ p ⟨
  p * 0ℚ <⟨ *-monoʳ-<-neg p (negative⁻¹ q) ⟩
  p * q  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _⊓_
------------------------------------------------------------------------

p≤q⇒p⊔q≡q : p ≤ q → p ⊔ q ≡ q
p≤q⇒p⊔q≡q {p@record{}} {q@record{}} p≤q with p ≤ᵇ q in p≰q
... | true  = refl
... | false = contradiction (≤⇒≤ᵇ p≤q) (subst (¬_ ∘ T) (sym p≰q) λ())

p≥q⇒p⊔q≡p : p ≥ q → p ⊔ q ≡ p
p≥q⇒p⊔q≡p {p@record{}} {q@record{}} p≥q with p ≤ᵇ q in p≤q
... | true  = ≤-antisym p≥q (≤ᵇ⇒≤ (subst T (sym p≤q) _))
... | false = refl

p≤q⇒p⊓q≡p : p ≤ q → p ⊓ q ≡ p
p≤q⇒p⊓q≡p {p@record{}} {q@record{}} p≤q with p ≤ᵇ q in p≰q
... | true  = refl
... | false = contradiction (≤⇒≤ᵇ p≤q) (subst (¬_ ∘ T) (sym p≰q) λ())

p≥q⇒p⊓q≡q : p ≥ q → p ⊓ q ≡ q
p≥q⇒p⊓q≡q {p@record{}} {q@record{}} p≥q with p ≤ᵇ q in p≤q
... | true  = ≤-antisym (≤ᵇ⇒≤ (subst T (sym p≤q) _)) p≥q
... | false = refl

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = p≤q⇒p⊓q≡p
  ; x≥y⇒x⊓y≈y = p≥q⇒p⊓q≡q
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = p≤q⇒p⊔q≡q
  ; x≥y⇒x⊔y≈x = p≥q⇒p⊔q≡p
  }

------------------------------------------------------------------------
-- Automatically derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties        = MinMaxOp        ⊓-operator ⊔-operator
  module ⊓-⊔-latticeProperties = LatticeMinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
  using
  ( ⊓-idem                    -- : Idempotent _⊓_
  ; ⊓-sel                     -- : Selective _⊓_
  ; ⊓-assoc                   -- : Associative _⊓_
  ; ⊓-comm                    -- : Commutative _⊓_

  ; ⊔-idem                    -- : Idempotent _⊔_
  ; ⊔-sel                     -- : Selective _⊔_
  ; ⊔-assoc                   -- : Associative _⊔_
  ; ⊔-comm                    -- : Commutative _⊔_

  ; ⊓-distribˡ-⊔              -- : _⊓_ DistributesOverˡ _⊔_
  ; ⊓-distribʳ-⊔              -- : _⊓_ DistributesOverʳ _⊔_
  ; ⊓-distrib-⊔               -- : _⊓_ DistributesOver  _⊔_
  ; ⊔-distribˡ-⊓              -- : _⊔_ DistributesOverˡ _⊓_
  ; ⊔-distribʳ-⊓              -- : _⊔_ DistributesOverʳ _⊓_
  ; ⊔-distrib-⊓               -- : _⊔_ DistributesOver  _⊓_
  ; ⊓-absorbs-⊔               -- : _⊓_ Absorbs _⊔_
  ; ⊔-absorbs-⊓               -- : _⊔_ Absorbs _⊓_
  ; ⊔-⊓-absorptive            -- : Absorptive _⊔_ _⊓_
  ; ⊓-⊔-absorptive            -- : Absorptive _⊓_ _⊔_

  ; ⊓-isMagma                 -- : IsMagma _⊓_
  ; ⊓-isSemigroup             -- : IsSemigroup _⊓_
  ; ⊓-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊓_
  ; ⊓-isBand                  -- : IsBand _⊓_
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _⊓_

  ; ⊔-isMagma                 -- : IsMagma _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊔_
  ; ⊔-isBand                  -- : IsBand _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊓-glb                     -- : ∀ {p q r} → p ≥ r → q ≥ r → p ⊓ q ≥ r
  ; ⊓-triangulate             -- : ∀ p q r → p ⊓ q ⊓ r ≡ (p ⊓ q) ⊓ (q ⊓ r)
  ; ⊓-mono-≤                  -- : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊓-monoˡ-≤                 -- : ∀ p → (_⊓ p) Preserves _≤_ ⟶ _≤_
  ; ⊓-monoʳ-≤                 -- : ∀ p → (p ⊓_) Preserves _≤_ ⟶ _≤_

  ; ⊔-lub                     -- : ∀ {p q r} → p ≤ r → q ≤ r → p ⊔ q ≤ r
  ; ⊔-triangulate             -- : ∀ p q r → p ⊔ q ⊔ r ≡ (p ⊔ q) ⊔ (q ⊔ r)
  ; ⊔-mono-≤                  -- : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊔-monoˡ-≤                 -- : ∀ p → (_⊔ p) Preserves _≤_ ⟶ _≤_
  ; ⊔-monoʳ-≤                 -- : ∀ p → (p ⊔_) Preserves _≤_ ⟶ _≤_
  )
  renaming
  ( x⊓y≈y⇒y≤x to p⊓q≡q⇒q≤p    -- : ∀ {p q} → p ⊓ q ≡ q → q ≤ p
  ; x⊓y≈x⇒x≤y to p⊓q≡p⇒p≤q    -- : ∀ {p q} → p ⊓ q ≡ p → p ≤ q
  ; x⊓y≤x     to p⊓q≤p        -- : ∀ p q → p ⊓ q ≤ p
  ; x⊓y≤y     to p⊓q≤q        -- : ∀ p q → p ⊓ q ≤ q
  ; x≤y⇒x⊓z≤y to p≤q⇒p⊓r≤q    -- : ∀ {p q} r → p ≤ q → p ⊓ r ≤ q
  ; x≤y⇒z⊓x≤y to p≤q⇒r⊓p≤q    -- : ∀ {p q} r → p ≤ q → r ⊓ p ≤ q
  ; x≤y⊓z⇒x≤y to p≤q⊓r⇒p≤q    -- : ∀ {p} q r → p ≤ q ⊓ r → p ≤ q
  ; x≤y⊓z⇒x≤z to p≤q⊓r⇒p≤r    -- : ∀ {p} q r → p ≤ q ⊓ r → p ≤ r

  ; x⊔y≈y⇒x≤y to p⊔q≡q⇒p≤q    -- : ∀ {p q} → p ⊔ q ≡ q → p ≤ q
  ; x⊔y≈x⇒y≤x to p⊔q≡p⇒q≤p    -- : ∀ {p q} → p ⊔ q ≡ p → q ≤ p
  ; x≤x⊔y     to p≤p⊔q        -- : ∀ p q → p ≤ p ⊔ q
  ; x≤y⊔x     to p≤q⊔p        -- : ∀ p q → p ≤ q ⊔ p
  ; x≤y⇒x≤y⊔z to p≤q⇒p≤q⊔r    -- : ∀ {p q} r → p ≤ q → p ≤ q ⊔ r
  ; x≤y⇒x≤z⊔y to p≤q⇒p≤r⊔q    -- : ∀ {p q} r → p ≤ q → p ≤ r ⊔ q
  ; x⊔y≤z⇒x≤z to p⊔q≤r⇒p≤r    -- : ∀ p q {r} → p ⊔ q ≤ r → p ≤ r
  ; x⊔y≤z⇒y≤z to p⊔q≤r⇒q≤r    -- : ∀ p q {r} → p ⊔ q ≤ r → q ≤ r

  ; x⊓y≤x⊔y   to p⊓q≤p⊔q      -- : ∀ p q → p ⊓ q ≤ p ⊔ q
  )

open ⊓-⊔-latticeProperties public
  using
  ( ⊓-isSemilattice           -- : IsSemilattice _⊓_
  ; ⊔-isSemilattice           -- : IsSemilattice _⊔_
  ; ⊔-⊓-isLattice             -- : IsLattice _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _⊓_ _⊔_

  ; ⊓-semilattice             -- : Semilattice _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _
  )

------------------------------------------------------------------------
-- Other properties of _⊓_ and _⊔_

mono-≤-distrib-⊔ : ∀ {f} → Monotonic₁ _≤_ _≤_ f →
                   ∀ p q → f (p ⊔ q) ≡ f p ⊔ f q
mono-≤-distrib-⊔ {f} = ⊓-⊔-properties.mono-≤-distrib-⊔ (cong f)

mono-≤-distrib-⊓ : ∀ {f} → Monotonic₁ _≤_ _≤_ f →
                   ∀ p q → f (p ⊓ q) ≡ f p ⊓ f q
mono-≤-distrib-⊓ {f} = ⊓-⊔-properties.mono-≤-distrib-⊓ (cong f)

mono-<-distrib-⊓ : ∀ {f} → Monotonic₁ _<_ _<_ f →
                   ∀ p q → f (p ⊓ q) ≡ f p ⊓ f q
mono-<-distrib-⊓ {f} f-mono-< p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊓ q)  ≡⟨ cong f (p≤q⇒p⊓q≡p (<⇒≤ p<q)) ⟩
  f p        ≡⟨ p≤q⇒p⊓q≡p (<⇒≤ (f-mono-< p<q)) ⟨
  f p ⊓ f q  ∎
  where open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊓ q)  ≡⟨ cong f (⊓-idem p) ⟩
  f p        ≡⟨ ⊓-idem (f p) ⟨
  f p ⊓ f q  ∎
  where open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊓ q)  ≡⟨ cong f (p≥q⇒p⊓q≡q (<⇒≤ p>q)) ⟩
  f q        ≡⟨ p≥q⇒p⊓q≡q (<⇒≤ (f-mono-< p>q)) ⟨
  f p ⊓ f q  ∎
  where open ≡-Reasoning

mono-<-distrib-⊔ : ∀ {f} → Monotonic₁ _<_ _<_ f →
                   ∀ p q → f (p ⊔ q) ≡ f p ⊔ f q
mono-<-distrib-⊔ {f} f-mono-< p q with <-cmp p q
... | tri< p<q p≢r  p≯q = begin
  f (p ⊔ q)  ≡⟨ cong f (p≤q⇒p⊔q≡q (<⇒≤ p<q)) ⟩
  f q        ≡⟨ p≤q⇒p⊔q≡q (<⇒≤ (f-mono-< p<q)) ⟨
  f p ⊔ f q  ∎
  where open ≡-Reasoning
... | tri≈ p≮q refl p≯q = begin
  f (p ⊔ q)  ≡⟨ cong f (⊔-idem p) ⟩
  f q        ≡⟨ ⊔-idem (f p) ⟨
  f p ⊔ f q  ∎
  where open ≡-Reasoning
... | tri> p≮q p≡r  p>q = begin
  f (p ⊔ q)  ≡⟨ cong f (p≥q⇒p⊔q≡p (<⇒≤ p>q)) ⟩
  f p        ≡⟨ p≥q⇒p⊔q≡p (<⇒≤ (f-mono-< p>q)) ⟨
  f p ⊔ f q  ∎
  where open ≡-Reasoning

antimono-≤-distrib-⊓ : ∀ {f} → Monotonic₁ _≤_ _≥_ f →
                       ∀ p q → f (p ⊓ q) ≡ f p ⊔ f q
antimono-≤-distrib-⊓ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊔ : ∀ {f} → Monotonic₁ _≤_ _≥_ f →
                       ∀ p q → f (p ⊔ q) ≡ f p ⊓ f q
antimono-≤-distrib-⊔ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊔ (cong f)

------------------------------------------------------------------------
-- Properties of _⊓_ and _*_

*-distribˡ-⊓-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊓ (p * r)
*-distribˡ-⊓-nonNeg p = mono-≤-distrib-⊓ (*-monoˡ-≤-nonNeg p)

*-distribʳ-⊓-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊓ (r * p)
*-distribʳ-⊓-nonNeg p = mono-≤-distrib-⊓ (*-monoʳ-≤-nonNeg p)

*-distribˡ-⊔-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊔ (p * r)
*-distribˡ-⊔-nonNeg p = mono-≤-distrib-⊔ (*-monoˡ-≤-nonNeg p)

*-distribʳ-⊔-nonNeg : ∀ p .{{_ : NonNegative p}} → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊔ (r * p)
*-distribʳ-⊔-nonNeg p = mono-≤-distrib-⊔ (*-monoʳ-≤-nonNeg p)

------------------------------------------------------------------------
-- Properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊔-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → p * (q ⊔ r) ≡ (p * q) ⊓ (p * r)
*-distribˡ-⊔-nonPos p = antimono-≤-distrib-⊔ (*-monoˡ-≤-nonPos p)

*-distribʳ-⊔-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → (q ⊔ r) * p ≡ (q * p) ⊓ (r * p)
*-distribʳ-⊔-nonPos p = antimono-≤-distrib-⊔ (*-monoʳ-≤-nonPos p)

*-distribˡ-⊓-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → p * (q ⊓ r) ≡ (p * q) ⊔ (p * r)
*-distribˡ-⊓-nonPos p = antimono-≤-distrib-⊓ (*-monoˡ-≤-nonPos p)

*-distribʳ-⊓-nonPos : ∀ p .{{_ : NonPositive p}} → ∀ q r → (q ⊓ r) * p ≡ (q * p) ⊔ (r * p)
*-distribʳ-⊓-nonPos p = antimono-≤-distrib-⊓ (*-monoʳ-≤-nonPos p)

------------------------------------------------------------------------
-- Properties of 1/_
------------------------------------------------------------------------

nonZero⇒1/nonZero : ∀ p .{{_ : NonZero p}} → NonZero (1/ p)
nonZero⇒1/nonZero (mkℚ +[1+ _ ] _ _) = _
nonZero⇒1/nonZero (mkℚ -[1+ _ ] _ _) = _

1/-involutive : ∀ p .{{_ : NonZero p}} → (1/ (1/ p)) {{nonZero⇒1/nonZero p}} ≡ p
1/-involutive (mkℚ +[1+ n ] d-1 _) = refl
1/-involutive (mkℚ -[1+ n ] d-1 _) = refl

1/pos⇒pos : ∀ p .{{_ : Positive p}} → Positive ((1/ p) {{pos⇒nonZero p}})
1/pos⇒pos (mkℚ +[1+ _ ] _ _) = _

1/neg⇒neg : ∀ p .{{_ : Negative p}} → Negative ((1/ p) {{neg⇒nonZero p}})
1/neg⇒neg (mkℚ -[1+ _ ] _ _) = _

pos⇒1/pos : ∀ p .{{_ : NonZero p}} .{{_ : Positive (1/ p)}} → Positive p
pos⇒1/pos p = subst Positive (1/-involutive p) (1/pos⇒pos (1/ p))

neg⇒1/neg : ∀ p .{{_ : NonZero p}} .{{_ : Negative (1/ p)}} → Negative p
neg⇒1/neg p = subst Negative (1/-involutive p) (1/neg⇒neg (1/ p))

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Monomorphic to unnormalised -_

toℚᵘ-homo-∣-∣ : Homomorphic₁ toℚᵘ ∣_∣ ℚᵘ.∣_∣
toℚᵘ-homo-∣-∣ (mkℚ +[1+ _ ] _ _) = *≡* refl
toℚᵘ-homo-∣-∣ (mkℚ +0       _ _) = *≡* refl
toℚᵘ-homo-∣-∣ (mkℚ -[1+ _ ] _ _) = *≡* refl

------------------------------------------------------------------------
-- Properties

∣p∣≡0⇒p≡0 : ∀ p → ∣ p ∣ ≡ 0ℚ → p ≡ 0ℚ
∣p∣≡0⇒p≡0 (mkℚ +0 zero _) ∣p∣≡0 = refl

0≤∣p∣ : ∀ p → 0ℚ ≤ ∣ p ∣
0≤∣p∣ p@record{} = *≤* (begin
  (↥ 0ℚ) ℤ.* (↧ ∣ p ∣)  ≡⟨ ℤ.*-zeroˡ (↧ ∣ p ∣) ⟩
  0ℤ                    ≤⟨ ℤ.+≤+ ℕ.z≤n ⟩
  ↥ ∣ p ∣               ≡⟨ ℤ.*-identityʳ (↥ ∣ p ∣) ⟨
  ↥ ∣ p ∣ ℤ.* 1ℤ        ∎)
  where open ℤ.≤-Reasoning

0≤p⇒∣p∣≡p : 0ℚ ≤ p → ∣ p ∣ ≡ p
0≤p⇒∣p∣≡p {p@record{}} 0≤p = toℚᵘ-injective (ℚᵘ.0≤p⇒∣p∣≃p (toℚᵘ-mono-≤ 0≤p))

∣-p∣≡∣p∣ : ∀ p → ∣ - p ∣ ≡ ∣ p ∣
∣-p∣≡∣p∣ (mkℚ +[1+ n ] d-1 _) = refl
∣-p∣≡∣p∣ (mkℚ +0       d-1 _) = refl
∣-p∣≡∣p∣ (mkℚ -[1+ n ] d-1 _) = refl

∣p∣≡p⇒0≤p : ∀ {p} → ∣ p ∣ ≡ p → 0ℚ ≤ p
∣p∣≡p⇒0≤p {p} ∣p∣≡p = toℚᵘ-cancel-≤ (ℚᵘ.∣p∣≃p⇒0≤p (begin-equality
  ℚᵘ.∣ toℚᵘ p ∣  ≃⟨ ℚᵘ.≃-sym (toℚᵘ-homo-∣-∣ p) ⟩
  toℚᵘ ∣ p ∣     ≡⟨ cong toℚᵘ ∣p∣≡p ⟩
  toℚᵘ p         ∎))
  where open ℚᵘ.≤-Reasoning

∣p∣≡p∨∣p∣≡-p : ∀ p → ∣ p ∣ ≡ p ⊎ ∣ p ∣ ≡ - p
∣p∣≡p∨∣p∣≡-p (mkℚ (+ n) d-1 _) = inj₁ refl
∣p∣≡p∨∣p∣≡-p (mkℚ (-[1+ n ]) d-1 _) = inj₂ refl

∣p+q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p+q∣≤∣p∣+∣q∣ p q = toℚᵘ-cancel-≤ (begin
  toℚᵘ ∣ p + q ∣                    ≃⟨ toℚᵘ-homo-∣-∣ (p + q) ⟩
  ℚᵘ.∣ toℚᵘ (p + q) ∣               ≃⟨ ℚᵘ.∣-∣-cong (toℚᵘ-homo-+ p q) ⟩
  ℚᵘ.∣ toℚᵘ p ℚᵘ.+ toℚᵘ q ∣         ≤⟨ ℚᵘ.∣p+q∣≤∣p∣+∣q∣ (toℚᵘ p) (toℚᵘ q) ⟩
  ℚᵘ.∣ toℚᵘ p ∣ ℚᵘ.+ ℚᵘ.∣ toℚᵘ q ∣  ≃⟨ ℚᵘ.+-cong (toℚᵘ-homo-∣-∣ p) (toℚᵘ-homo-∣-∣ q) ⟨
  toℚᵘ ∣ p ∣ ℚᵘ.+ toℚᵘ ∣ q ∣        ≃⟨ toℚᵘ-homo-+ ∣ p ∣ ∣ q ∣ ⟨
  toℚᵘ (∣ p ∣ + ∣ q ∣)              ∎)
  where open ℚᵘ.≤-Reasoning

∣p-q∣≤∣p∣+∣q∣ : ∀ p q → ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p-q∣≤∣p∣+∣q∣ p@record{} q@record{} = begin
  ∣ p   -     q ∣  ≤⟨ ∣p+q∣≤∣p∣+∣q∣ p (- q) ⟩
  ∣ p ∣ + ∣ - q ∣  ≡⟨ cong (λ h → ∣ p ∣ + h) (∣-p∣≡∣p∣ q) ⟩
  ∣ p ∣ + ∣   q ∣  ∎
  where open ≤-Reasoning

∣p*q∣≡∣p∣*∣q∣ : ∀ p q → ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
∣p*q∣≡∣p∣*∣q∣ p q = toℚᵘ-injective (begin-equality
  toℚᵘ ∣ p * q ∣                    ≃⟨ toℚᵘ-homo-∣-∣ (p * q) ⟩
  ℚᵘ.∣ toℚᵘ (p * q) ∣               ≃⟨ ℚᵘ.∣-∣-cong (toℚᵘ-homo-* p q) ⟩
  ℚᵘ.∣ toℚᵘ p ℚᵘ.* toℚᵘ q ∣         ≃⟨ ℚᵘ.∣p*q∣≃∣p∣*∣q∣ (toℚᵘ p) (toℚᵘ q) ⟩
  ℚᵘ.∣ toℚᵘ p ∣ ℚᵘ.* ℚᵘ.∣ toℚᵘ q ∣  ≃⟨ ℚᵘ.*-cong (toℚᵘ-homo-∣-∣ p) (toℚᵘ-homo-∣-∣ q) ⟨
  toℚᵘ ∣ p ∣ ℚᵘ.* toℚᵘ ∣ q ∣        ≃⟨ toℚᵘ-homo-* ∣ p ∣ ∣ q ∣ ⟨
  toℚᵘ (∣ p ∣ * ∣ q ∣)              ∎)
  where open ℚᵘ.≤-Reasoning

∣-∣-nonNeg : ∀ p → NonNegative ∣ p ∣
∣-∣-nonNeg (mkℚ +[1+ _ ] _ _) = _
∣-∣-nonNeg (mkℚ +0       _ _) = _
∣-∣-nonNeg (mkℚ -[1+ _ ] _ _) = _

∣∣p∣∣≡∣p∣ : ∀ p → ∣ ∣ p ∣ ∣ ≡ ∣ p ∣
∣∣p∣∣≡∣p∣ p = 0≤p⇒∣p∣≡p (0≤∣p∣ p)

------------------------------------------------------------------------
-- Other properties of _+_
------------------------------------------------------------------------

i/n+j/n≡[i+j]/n : ∀ (i j : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n }} →
                  i / n + j / n ≡ (i ℤ.+ j) / n
i/n+j/n≡[i+j]/n i j n = begin
  i / n + j / n
    ≡⟨ +-def ⟩
  (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) / (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ)
    ≡⟨ *-cancelʳ-/ gcd[j,n]ₙ
                   {↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ}
                   { ↧ₙ pᵢ ℕ.* ↧ₙ qⱼ }
     ⟨
  (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) ℤ.* gcd[j,n]
    / (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ)
    ≡⟨ *-cancelʳ-/ gcd[i,n]ₙ
                   { (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) ℤ.* gcd[j,n] }
                   { ↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ }
     ⟨
  (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) ℤ.* gcd[j,n] ℤ.* gcd[i,n]
    / (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ ℕ.* gcd[i,n]ₙ)
    ≡⟨ /-cong ↥≡ ↧≡ ⟩
  (i ℤ.+ j) ℤ.* + n / (n ℕ.* n)
    ≡⟨ *-cancelʳ-/ n {i ℤ.+ j} {n} ⟩
  (i ℤ.+ j) / n
    ∎
  where
  open ≡-Reasoning

  pᵢ = i / n
  qⱼ = j / n
  gcd[i,n]ₙ = ℕ.gcd ℤ.∣ i ∣ n
  gcd[i,n]  = + gcd[i,n]ₙ
  gcd[j,n]ₙ = ℕ.gcd ℤ.∣ j ∣ n
  gcd[j,n]  = + gcd[j,n]ₙ

  instance
    _ = ℕ.≢-nonZero $ ℕ.gcd[m,n]≢0 ℤ.∣ i ∣ n $ inj₂ $ ℕ.≢-nonZero⁻¹ n
    _ = ℕ.≢-nonZero $ ℕ.gcd[m,n]≢0 ℤ.∣ j ∣ n $ inj₂ $ ℕ.≢-nonZero⁻¹ n
    _ = ℕ.m*n≢0 (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ) gcd[j,n]ₙ
    _ = ℕ.m*n≢0 (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ) gcd[i,n]ₙ
    _ = ℕ.m*n≢0 n n

  +-def : pᵢ + qⱼ ≡ (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) / (↧ₙ pᵢ ℕ.* ↧ₙ qⱼ)
  +-def with record{} ← pᵢ with record{} ← qⱼ = refl

  ↥≡ : (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) ℤ.* gcd[j,n] ℤ.* gcd[i,n]
     ≡ (i ℤ.+ j) ℤ.* + n
  ↥≡ = begin
    (↥ pᵢ ℤ.* ↧ qⱼ ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ) ℤ.* gcd[j,n] ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._* gcd[i,n])
       $ ℤ.*-distribʳ-+ gcd[j,n]
           (↥ pᵢ ℤ.* ↧ qⱼ)
           (↥ qⱼ ℤ.* ↧ pᵢ)
       ⟩
    (↥ pᵢ ℤ.* ↧ qⱼ ℤ.* gcd[j,n] ℤ.+ ↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n]) ℤ.* gcd[i,n]
      ≡⟨ ℤ.*-distribʳ-+ gcd[i,n]
           (↥ pᵢ ℤ.* ↧ qⱼ ℤ.* gcd[j,n])
           (↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n])
       ⟩
    ↥ pᵢ ℤ.* ↧ qⱼ ℤ.* gcd[j,n] ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n] ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+ ↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n] ℤ.* gcd[i,n])
       $ cong (ℤ._* gcd[i,n])
       $ ℤ.*-assoc (↥ pᵢ) (↧ qⱼ) gcd[j,n]
       ⟩
    ↥ pᵢ ℤ.* (↧ qⱼ ℤ.* gcd[j,n]) ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n] ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+ (↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n] ℤ.* gcd[i,n]))
       $ cong (ℤ._* gcd[i,n])
       $ cong (↥ pᵢ ℤ.*_)
       $ ↧-/ j n
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* ↧ pᵢ ℤ.* gcd[j,n] ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ cong (ℤ._* gcd[i,n])
       $ ℤ.*-assoc (↥ qⱼ) (↧ pᵢ) gcd[j,n]
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* (↧ pᵢ ℤ.* gcd[j,n]) ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ cong (ℤ._* gcd[i,n])
       $ cong (↥ qⱼ ℤ.*_)
       $ ℤ.*-comm (↧ pᵢ) gcd[j,n]
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* (gcd[j,n] ℤ.* ↧ pᵢ) ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ cong (ℤ._* gcd[i,n])
       $ ℤ.*-assoc (↥ qⱼ) gcd[j,n] (↧ pᵢ)
       ⟨
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+
    ↥ qⱼ ℤ.* gcd[j,n] ℤ.* ↧ pᵢ ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ cong (ℤ._* gcd[i,n])
       $ cong (ℤ._* ↧ pᵢ)
       $ ↥-/ j n
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+ j ℤ.* ↧ pᵢ ℤ.* gcd[i,n]
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ ℤ.*-assoc j (↧ pᵢ) gcd[i,n]
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+ j ℤ.* (↧ pᵢ ℤ.* gcd[i,n])
      ≡⟨ cong (ℤ._+_ (↥ pᵢ ℤ.* + n ℤ.* gcd[i,n]))
       $ cong (j ℤ.*_)
       $ ↧-/ i n
       ⟩
    ↥ pᵢ ℤ.* + n ℤ.* gcd[i,n] ℤ.+ j ℤ.* + n
      ≡⟨ cong (ℤ._+ j ℤ.* + n)
       $ cong (ℤ._* gcd[i,n])
       $ ℤ.*-comm (↥ pᵢ) (+ n)
       ⟩
    + n ℤ.* ↥ pᵢ ℤ.* gcd[i,n] ℤ.+ j ℤ.* + n
      ≡⟨ cong (ℤ._+ j ℤ.* + n)
       $ ℤ.*-assoc (+ n) (↥ pᵢ) gcd[i,n]
       ⟩
    + n ℤ.* (↥ pᵢ ℤ.* gcd[i,n]) ℤ.+ j ℤ.* + n
      ≡⟨ cong (ℤ._+ j ℤ.* + n)
       $ cong (+ n ℤ.*_)
       $ ↥-/ i n
       ⟩
    + n ℤ.* i ℤ.+ j ℤ.* + n
      ≡⟨ cong (ℤ._+ j ℤ.* + n)
       $ ℤ.*-comm (+ n) i
       ⟩
    i ℤ.* + n ℤ.+ j ℤ.* + n
      ≡⟨ ℤ.*-distribʳ-+ (+ n) i j ⟨
    (i ℤ.+ j) ℤ.* + n
      ∎

  ↧≡ : ↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ ℕ.* gcd[i,n]ₙ ≡ n ℕ.* n
  ↧≡ = begin
    ↧ₙ pᵢ ℕ.* ↧ₙ qⱼ ℕ.* gcd[j,n]ₙ ℕ.* gcd[i,n]ₙ
      ≡⟨ cong (ℕ._* gcd[i,n]ₙ)
       $ ℕ.*-assoc (↧ₙ pᵢ) (↧ₙ qⱼ) gcd[j,n]ₙ
       ⟩
    ↧ₙ pᵢ ℕ.* (↧ₙ qⱼ ℕ.* gcd[j,n]ₙ) ℕ.* gcd[i,n]ₙ
      ≡⟨ cong (ℕ._* gcd[i,n]ₙ)
       $ cong (↧ₙ pᵢ ℕ.*_)
       $ ℤ.abs-* (↧ qⱼ) (gcd j (+ n))
       ⟨
    ↧ₙ pᵢ ℕ.* ℤ.∣ (+ ↧ₙ qⱼ) ℤ.* gcd j (+ n) ∣ ℕ.* gcd[i,n]ₙ
      ≡⟨ cong (ℕ._* gcd[i,n]ₙ)
       $ cong (↧ₙ pᵢ ℕ.*_)
       $ cong ℤ.∣_∣
       $ ↧-/ j n
       ⟩
    ↧ₙ pᵢ ℕ.* n ℕ.* gcd[i,n]ₙ
      ≡⟨ cong (ℕ._* gcd[i,n]ₙ)
       $ ℕ.*-comm (↧ₙ pᵢ) n
       ⟩
    n ℕ.* ↧ₙ pᵢ ℕ.* gcd[i,n]ₙ
      ≡⟨ ℕ.*-assoc n (↧ₙ pᵢ) gcd[i,n]ₙ ⟩
    n ℕ.* (↧ₙ pᵢ ℕ.* gcd[i,n]ₙ)
      ≡⟨ cong (n ℕ.*_)
       $ ℤ.abs-* (↧ pᵢ) (gcd i (+ n))
       ⟨
    n ℕ.* ℤ.∣ + ↧ₙ pᵢ ℤ.* gcd i (+ n) ∣
      ≡⟨ cong (n ℕ.*_)
       $ cong ℤ.∣_∣
       $ ↧-/ i n
       ⟩
    n ℕ.* n
      ∎

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

*-monoʳ-≤-neg : ∀ r → Negative r → (_* r) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-neg r@(mkℚ -[1+ _ ] _ _) _ = *-monoʳ-≤-nonPos r
{-# WARNING_ON_USAGE *-monoʳ-≤-neg
"Warning: *-monoʳ-≤-neg was deprecated in v2.0.
Please use *-monoʳ-≤-nonPos instead."
#-}
*-monoˡ-≤-neg : ∀ r → Negative r → (r *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-neg r@(mkℚ -[1+ _ ] _ _) _ = *-monoˡ-≤-nonPos r
{-# WARNING_ON_USAGE *-monoˡ-≤-neg
"Warning: *-monoˡ-≤-neg was deprecated in v2.0.
Please use *-monoˡ-≤-nonPos instead."
#-}
*-monoʳ-≤-pos : ∀ r → Positive r → (_* r) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos r@(mkℚ +[1+ _ ] _ _) _ = *-monoʳ-≤-nonNeg r
{-# WARNING_ON_USAGE *-monoʳ-≤-pos
"Warning: *-monoʳ-≤-pos was deprecated in v2.0.
Please use *-monoʳ-≤-nonNeg instead."
#-}
*-monoˡ-≤-pos : ∀ r → Positive r → (r *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos r@(mkℚ +[1+ _ ] _ _) _ = *-monoˡ-≤-nonNeg r
{-# WARNING_ON_USAGE *-monoˡ-≤-pos
"Warning: *-monoˡ-≤-pos was deprecated in v2.0.
Please use *-monoˡ-≤-nonNeg instead."
#-}
*-cancelˡ-<-pos : ∀ r → Positive r → ∀ {p q} → r * p < r * q → p < q
*-cancelˡ-<-pos r@(mkℚ +[1+ _ ] _ _) _ = *-cancelˡ-<-nonNeg r
{-# WARNING_ON_USAGE *-cancelˡ-<-pos
"Warning: *-cancelˡ-<-pos was deprecated in v2.0.
Please use *-cancelˡ-<-nonNeg instead."
#-}
*-cancelʳ-<-pos : ∀ r → Positive r → ∀ {p q} → p * r < q * r → p < q
*-cancelʳ-<-pos r@(mkℚ +[1+ _ ] _ _) _ = *-cancelʳ-<-nonNeg r
{-# WARNING_ON_USAGE *-cancelʳ-<-pos
"Warning: *-cancelʳ-<-pos was deprecated in v2.0.
Please use *-cancelʳ-<-nonNeg instead."
#-}
*-cancelˡ-<-neg : ∀ r → Negative r → ∀ {p q} → r * p < r * q → p > q
*-cancelˡ-<-neg r@(mkℚ -[1+ _ ] _ _) _ = *-cancelˡ-<-nonPos r
{-# WARNING_ON_USAGE *-cancelˡ-<-neg
"Warning: *-cancelˡ-<-neg was deprecated in v2.0.
Please use *-cancelˡ-<-nonPos instead."
#-}
*-cancelʳ-<-neg : ∀ r → Negative r → ∀ {p q} → p * r < q * r → p > q
*-cancelʳ-<-neg r@(mkℚ -[1+ _ ] _ _) _ = *-cancelʳ-<-nonPos r
{-# WARNING_ON_USAGE *-cancelʳ-<-neg
"Warning: *-cancelʳ-<-neg was deprecated in v2.0.
Please use *-cancelʳ-<-nonPos instead."
#-}
negative<positive : Negative p → Positive q → p < q
negative<positive {p} {q} p<0 q>0 = neg<pos p q {{p<0}} {{q>0}}
{-# WARNING_ON_USAGE negative<positive
"Warning: negative<positive was deprecated in v2.0.
Please use neg<pos instead."
#-}
{- issue1865/issue1755: raw bundles have moved to `Data.X.Base` -}
open Data.Rational.Base public
  using (+-rawMagma; +-0-rawGroup; *-rawMagma; +-*-rawNearSemiring; +-*-rawSemiring; +-*-rawRing)
  renaming (+-0-rawMonoid to +-rawMonoid; *-1-rawMonoid to *-rawMonoid)

-- Version 2.4

nonPos*nonPos⇒nonPos = nonPos*nonPos⇒nonNeg
{-# WARNING_ON_USAGE nonPos*nonPos⇒nonPos
"Warning: nonPos*nonPos⇒nonPos was deprecated in v2.4.
Please use nonPos*nonPos⇒nonNeg instead."
#-}

-- Version 3.0

infix 4 _≟_
_≟_ = _≡?_
{-# WARNING_ON_USAGE _≟_
"Warning: _≟_ was deprecated in v3.0.
Please use _≡?_ instead."
#-}

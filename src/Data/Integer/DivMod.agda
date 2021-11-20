------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.DivMod where

open import Data.Integer.Base
open import Data.Integer.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as ℕ
import Data.Sign as S
open import Function.Base using (_∘′_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition

infixl 7 _divℕ_ _div_ _modℕ_ _mod_
_divℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℤ
(+ n      divℕ d) = + (n ℕ./ d)
(-[1+ n ] divℕ d) with ℕ.suc n ℕ.% d
... | ℕ.zero  = - (+ (ℕ.suc n ℕ./ d))
... | ℕ.suc r = -[1+ (ℕ.suc n ℕ./ d) ]

_div_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℤ
n div d = (sign d ◃ 1) * (n divℕ ∣ d ∣)

_modℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℕ
(+ n      modℕ d) = n ℕ.% d
(-[1+ n ] modℕ d) with ℕ.suc n ℕ.% d
... | ℕ.zero      = 0
... | r@(ℕ.suc _) = d ℕ.∸ r

_mod_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℕ
n mod d = n modℕ ∣ d ∣

------------------------------------------------------------------------
-- Properties

n%ℕd<d : ∀ n d .{{_ : ℕ.NonZero d}} → n modℕ d ℕ.< d
n%ℕd<d (+ n)    d           = ℕ.m%n<n n d
n%ℕd<d -[1+ n ] d@(ℕ.suc _) with ℕ.suc n ℕ.% d
... | ℕ.zero  = ℕ.s≤s ℕ.z≤n
... | ℕ.suc r = ℕ.s≤s (ℕ.m∸n≤m _ r)

n%d<d : ∀ n d .{{_ : NonZero d}} → n mod d ℕ.< ∣ d ∣
n%d<d n (+ d)    = n%ℕd<d n d
n%d<d n -[1+ d ] = n%ℕd<d n (ℕ.suc d)

a≡a%ℕn+[a/ℕn]*n : ∀ n d .{{_ : ℕ.NonZero d}} → n ≡ + (n modℕ d) + (n divℕ d) * + d
a≡a%ℕn+[a/ℕn]*n (+ n) d = let q = n ℕ./ d; r = n ℕ.% d in begin-equality
  + n                ≡⟨ cong +_ (ℕ.m≡m%n+[m/n]*n n d) ⟩
  + (r ℕ.+ q ℕ.* d)  ≡⟨ pos-+-commute r (q ℕ.* d) ⟩
  + r + + (q ℕ.* d)  ≡⟨ cong (_+_ (+ r)) (sym (pos-distrib-* q d)) ⟩
  + r + + q * + d    ∎
a≡a%ℕn+[a/ℕn]*n n@(-[1+ _ ]) d with ∣ n ∣ ℕ.% d in eq
... | ℕ.zero = begin-equality
  n                   ≡⟨ cong (-_ ∘′ +_) (ℕ.m≡m%n+[m/n]*n ∣n∣ d) ⟩
  - + (r ℕ.+ q ℕ.* d) ≡⟨ cong (-_ ∘′ +_) (cong (ℕ._+ q ℕ.* d) eq) ⟩
  - + (q ℕ.* d)       ≡⟨ cong -_ (sym (pos-distrib-* q d)) ⟩
  - (+ q * + d)       ≡⟨ neg-distribˡ-* (+ q) (+ d) ⟩
  - (+ q) * + d       ≡⟨ sym (+-identityˡ (- (+ q) * + d)) ⟩
  + 0 + - (+ q) * + d ∎
  where ∣n∣ = ∣ n ∣; q = ∣n∣ ℕ./ d; r = ∣n∣ ℕ.% d
... | r@(ℕ.suc _) = begin-equality
  let ∣n∣ = ∣ n ∣; q = ∣n∣ ℕ./ d; r′ = ∣n∣ ℕ.% d in
  n                                      ≡⟨ cong (-_ ∘′ +_) (ℕ.m≡m%n+[m/n]*n ∣n∣ d) ⟩
  - + (r′ ℕ.+ q ℕ.* d)                   ≡⟨ cong (-_ ∘′ +_) (cong (ℕ._+ q ℕ.* d) eq) ⟩
  - + (r  ℕ.+ q ℕ.* d)                   ≡⟨ cong -_ (pos-+-commute r (q ℕ.* d)) ⟩
  - (+ r + + (q ℕ.* d))                  ≡⟨ neg-distrib-+ (+ r) (+ (q ℕ.* d)) ⟩
  - + r - + (q ℕ.* d)                    ≡⟨ cong (_-_ (- + r)) (sym (pos-distrib-* q d)) ⟩
  - + r - (+ q * + d)                    ≡⟨⟩
  - + r - pred +[1+ q ] * + d            ≡⟨ cong (_-_ (- + r)) (*-distribʳ-+ (+ d) -1ℤ +[1+ q ]) ⟩
  - + r - (-1ℤ * + d + (+[1+ q ] * + d)) ≡⟨ cong (λ v → - + r - (v + (+[1+ q ] * + d))) (-1*i≡-i (+ d))  ⟩
  - + r - (- + d     + (+[1+ q ] * + d)) ≡⟨ cong (_+_ (- + r)) (neg-distrib-+ (- + d) (+[1+ q ] * + d)) ⟩
  - + r + (- - + d + - (+[1+ q ] * + d)) ≡⟨ cong (λ v → - + r + (v + - (+[1+ q ] * + d))) (neg-involutive (+ d))  ⟩
  - + r + (+ d     + - (+[1+ q ] * + d)) ≡⟨ cong (λ v → - + r + (+ d + v)) (neg-distribˡ-* +[1+ q ] (+ d)) ⟩
  - + r + (+ d     +   (-[1+ q ] * + d)) ≡⟨ sym (+-assoc (- + r) (+ d) (-[1+ q ] * + d)) ⟩
  - + r + + d      +   (-[1+ q ] * + d)  ≡⟨ cong (_+ -[1+ q ] * + d) (-m+n≡n⊖m r d) ⟩
  d ⊖ r            +   (-[1+ q ] * + d)  ≡⟨ cong (_+ -[1+ q ] * + d) (⊖-≥ (subst (ℕ._≤ d) eq (ℕ.m%n≤n ∣n∣ d))) ⟩
  + (d ℕ.∸ r)      +   (-[1+ q ] * + d)  ∎

[n/ℕd]*d≤n : ∀ n d .{{_ : ℕ.NonZero d}} → (n divℕ d) * + d ≤ n
[n/ℕd]*d≤n n d = let q = n divℕ d; r = n modℕ d in begin
  q * + d        ≤⟨  i≤j+i _ (+ r) ⟩
  + r + q * + d  ≡˘⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  n              ∎

div-pos-is-divℕ : ∀ n d .{{_ : ℕ.NonZero d}} →
                  n div (+ d) ≡ n divℕ d
div-pos-is-divℕ n (ℕ.suc d) = *-identityˡ (n divℕ ℕ.suc d)

div-neg-is-neg-divℕ : ∀ n d .{{_ : ℕ.NonZero d}} .{{_ : NonZero (- + d)}} →
                      n div (- + d) ≡ - (n divℕ d)
div-neg-is-neg-divℕ n (ℕ.suc d) = -1*i≡-i (n divℕ ℕ.suc d)

0≤n⇒0≤n/ℕd : ∀ n d .{{_ : ℕ.NonZero d}} → 0ℤ ≤ n → 0ℤ ≤ (n divℕ d)
0≤n⇒0≤n/ℕd (+ n) d (+≤+ m≤n) = +≤+ ℕ.z≤n

0≤n⇒0≤n/d : ∀ n d .{{_ : NonZero d}} → 0ℤ ≤ n → 0ℤ ≤ d → 0ℤ ≤ (n div d)
0≤n⇒0≤n/d n (+ d) {{d≢0}} 0≤n (+≤+ 0≤d)
  rewrite div-pos-is-divℕ n d {{d≢0}}
        = 0≤n⇒0≤n/ℕd n d 0≤n

[n/d]*d≤n : ∀ n d .{{_ : NonZero d}} → (n div d) * d ≤ n
[n/d]*d≤n n (+ d) = begin
  n div + d * + d        ≡⟨ cong (_* (+ d)) (div-pos-is-divℕ n d) ⟩
  n divℕ d  * + d        ≤⟨ [n/ℕd]*d≤n n d ⟩
  n                      ∎
[n/d]*d≤n n d@(-[1+ _ ]) = begin let ∣d∣ = ∣ d ∣ in
  n div d        * d     ≡⟨ cong (_* d) (div-neg-is-neg-divℕ n ∣d∣) ⟩
  - (n divℕ ∣d∣) * d     ≡⟨ sym (neg-distribˡ-* (n divℕ ∣d∣) d) ⟩
  - (n divℕ ∣d∣  * d)    ≡⟨ neg-distribʳ-* (n divℕ ∣d∣) d ⟩
  n divℕ ∣d∣     * + ∣d∣ ≤⟨ [n/ℕd]*d≤n n ∣d∣ ⟩
  n                      ∎

n<s[n/ℕd]*d : ∀ n d .{{_ : ℕ.NonZero d}} → n < suc (n divℕ d) * + d
n<s[n/ℕd]*d n d = begin-strict
  n                    ≡⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  + r + q * + d        <⟨ +-monoˡ-< (q * + d) (+<+ (n%ℕd<d n d)) ⟩
  + d + q * + d        ≡⟨ sym (suc-* q (+ d)) ⟩
  suc (n divℕ d) * + d ∎
  where q = n divℕ d; r = n modℕ d

a≡a%n+[a/n]*n : ∀ a n .{{_ : NonZero n}} → a ≡ + (a mod n) + (a div n) * n
a≡a%n+[a/n]*n n d@(+ _) = begin-equality
  let ∣d∣ = ∣ d ∣; r = n mod d; q = n divℕ ∣d∣ in
  n                  ≡⟨ a≡a%ℕn+[a/ℕn]*n n ∣d∣ ⟩
  + r + (q * + ∣d∣)  ≡⟨ cong (λ p → + r + p * d) (sym (div-pos-is-divℕ n ∣d∣)) ⟩
  + r + n div d * d  ∎
a≡a%n+[a/n]*n n d@(-[1+ _ ]) = begin-equality
  let ∣d∣ = ∣ d ∣; r = n mod d; q = n divℕ ∣d∣ in
  n                  ≡⟨ a≡a%ℕn+[a/ℕn]*n n ∣d∣ ⟩
  + r + q * + ∣d∣    ≡⟨⟩
  + r + q * - d      ≡⟨ cong (_+_ (+ r)) (sym (neg-distribʳ-* q d)) ⟩
  + r + - (q * d)    ≡⟨ cong (_+_ (+ r)) (neg-distribˡ-* q d) ⟩
  + r + - q * d      ≡⟨ cong (_+_ (+ r) ∘′ (_* d)) (sym (-1*i≡-i q)) ⟩
  + r + n div d * d  ∎

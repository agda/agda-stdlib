------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.DivMod where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base as Fin using (Fin)
import Data.Fin.Properties as FProp
open import Data.Integer.Base as ℤ
open import Data.Integer.Properties
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NProp
import Data.Nat.DivMod as NDM
import Data.Sign as S
import Data.Sign.Properties as SProp
open import Function
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definition

infixl 7 _divℕ_ _div_ _modℕ_ _mod_
_divℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℤ
(+ n      divℕ d) = + (n NDM./ d)
(-[1+ n ] divℕ d) with (ℕ.suc n NDM.divMod d)
... | NDM.result q Fin.zero    eq = - (+ q)
... | NDM.result q (Fin.suc r) eq = -[1+ q ]

_div_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℤ
n div d = (sign d ◃ 1) ℤ.* (n divℕ ∣ d ∣)

_modℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℕ
(+ n      modℕ d) = n NDM.% d
(-[1+ n ] modℕ d) with ℕ.suc n NDM.divMod d
... | NDM.result q Fin.zero    eq = 0
... | NDM.result q (Fin.suc r) eq = d ℕ.∸ ℕ.suc (Fin.toℕ r)

_mod_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℕ
n mod d = n modℕ ∣ d ∣

------------------------------------------------------------------------
-- Properties

n%ℕd<d : ∀ n d .{{_ : ℕ.NonZero d}} → n modℕ d ℕ.< d
n%ℕd<d (+ n)    d = NDM.m%n<n n d
n%ℕd<d -[1+ n ] d with ℕ.suc n NDM.divMod d
... | NDM.result q Fin.zero    eq = ℕ.s≤s ℕ.z≤n
... | NDM.result q (Fin.suc r) eq = ℕ.s≤s (NProp.m∸n≤m _ (Fin.toℕ r))

n%d<d : ∀ n d .{{_ : NonZero d}} → n mod d ℕ.< ℤ.∣ d ∣
n%d<d n (+ d)    = n%ℕd<d n d
n%d<d n -[1+ d ] = n%ℕd<d n (ℕ.suc d)

a≡a%ℕn+[a/ℕn]*n : ∀ n d .{{_ : ℕ.NonZero d}} → n ≡ + (n modℕ d) + (n divℕ d) * + d
a≡a%ℕn+[a/ℕn]*n (+ n) d = let q = n NDM./ d; r = n NDM.% d in begin
  + n                ≡⟨ cong +_ (NDM.m≡m%n+[m/n]*n n d) ⟩
  + (r ℕ.+ q ℕ.* d)  ≡⟨ pos-+-commute r (q ℕ.* d) ⟩
  + r + + (q ℕ.* d)  ≡⟨ cong (_+_ (+ (+ n modℕ d))) (sym (pos-distrib-* q d)) ⟩
  + r + + q * + d    ∎ where open ≡-Reasoning
a≡a%ℕn+[a/ℕn]*n -[1+ n ] d with (ℕ.suc n) NDM.divMod d
... | NDM.result q Fin.zero    eq = begin
  -[1+ n ]            ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (q ℕ.* d)       ≡⟨ cong -_ (sym (pos-distrib-* q d)) ⟩
  - (+ q * + d)       ≡⟨ neg-distribˡ-* (+ q) (+ d) ⟩
  - (+ q) * + d       ≡⟨ sym (+-identityˡ (- (+ q) * + d)) ⟩
  + 0 + - (+ q) * + d ∎ where open ≡-Reasoning
... | NDM.result q (Fin.suc r) eq = begin
  let sr = ℕ.suc (Fin.toℕ r); sq = ℕ.suc q in
  -[1+ n ]
    ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (sr ℕ.+ q ℕ.* d)
    ≡⟨ cong -_ (pos-+-commute sr (q ℕ.* d)) ⟩
  - (+ sr + + (q ℕ.* d))
    ≡⟨ neg-distrib-+ (+ sr) (+ (q ℕ.* d)) ⟩
  - + sr - + (q ℕ.* d)
    ≡⟨ cong (_-_ (- + sr)) (sym (pos-distrib-* q d)) ⟩
  - + sr - (+ q) * (+ d)
    ≡⟨⟩
  - + sr - pred (+ sq) * (+ d)
    ≡⟨ cong (_-_ (- + sr)) (*-distribʳ-+ (+ d) (- + 1)  (+ sq)) ⟩
  - + sr - (- (+ 1) * + d + (+ sq * + d))
    ≡⟨ cong (_+_ (- (+ sr))) (neg-distrib-+ (- (+ 1) * + d) (+ sq * + d)) ⟩
  - + sr + (- (-[1+ 0 ] * + d) + - (+ sq * + d))
    ≡⟨ cong₂ (λ p q → - + sr + (- p + q)) (-1*i≡-i (+ d))
                                            (neg-distribˡ-* (+ sq) (+ d)) ⟩
  - + sr + ((- - + d) + -[1+ q ] * + d)
    ≡⟨ sym (+-assoc (- + sr) (- - + d) (-[1+ q ] * + d)) ⟩
  (+ d - + sr) + -[1+ q ] * + d
    ≡⟨ cong (_+ -[1+ q ] * + d) (fin-inv _ r) ⟩
  + (d ℕ.∸ sr) + -[1+ q ] * + d
    ∎ where

    open ≡-Reasoning

    fin-inv : ∀ d (k : Fin d) → +[1+ d ] - +[1+ Fin.toℕ k ] ≡ + (d ℕ.∸ Fin.toℕ k)
    fin-inv d k = begin
      +[1+ d ] - +[1+ Fin.toℕ k ] ≡⟨ m-n≡m⊖n (ℕ.suc d) (ℕ.suc (Fin.toℕ k)) ⟩
      ℕ.suc d ⊖ ℕ.suc (Fin.toℕ k) ≡⟨ ⊖-≥ (ℕ.s≤s (FProp.toℕ≤n k)) ⟩
      + (d ℕ.∸ Fin.toℕ k)         ∎ where open ≡-Reasoning

[n/ℕd]*d≤n : ∀ n d .{{_ : ℕ.NonZero d}} → (n divℕ d) ℤ.* ℤ.+ d ℤ.≤ n
[n/ℕd]*d≤n n (ℕ.suc d) = let q = n divℕ ℕ.suc d; r = n modℕ ℕ.suc d in begin
  q ℤ.* ℤ.+ (ℕ.suc d)           ≤⟨ n≤m+n r ⟩
  ℤ.+ r ℤ.+ q ℤ.* ℤ.+ (ℕ.suc d) ≡⟨ sym (a≡a%ℕn+[a/ℕn]*n n (ℕ.suc d)) ⟩
  n                             ∎ where open ≤-Reasoning

div-pos-is-divℕ : ∀ n d .{{_ : ℕ.NonZero d}} → n div (+ d) ≡ n divℕ d
div-pos-is-divℕ n (ℕ.suc d) = *-identityˡ (n divℕ ℕ.suc d)

div-neg-is-neg-divℕ : ∀ n d .{{_ : ℕ.NonZero d}} .{{_ : NonZero (- + d)}} → n div (- + d) ≡ - (n divℕ d)
div-neg-is-neg-divℕ n (ℕ.suc d) = -1*i≡-i (n divℕ ℕ.suc d)

0≤n⇒0≤n/ℕd : ∀ n d .{{_ : ℕ.NonZero d}} → +0 ℤ.≤ n → +0 ℤ.≤ (n divℕ d)
0≤n⇒0≤n/ℕd (+ n) d (+≤+ m≤n) = +≤+ ℕ.z≤n

0≤n⇒0≤n/d : ∀ n d .{{_ : NonZero d}} → +0 ℤ.≤ n → +0 ℤ.≤ d → +0 ℤ.≤ (n div d)
0≤n⇒0≤n/d n (+ d) {{d≢0}} 0≤n (+≤+ 0≤d)
  rewrite div-pos-is-divℕ n d {{d≢0}}
        = 0≤n⇒0≤n/ℕd n d 0≤n

[n/d]*d≤n : ∀ n d .{{_ : NonZero d}} → (n div d) ℤ.* d ℤ.≤ n
[n/d]*d≤n n (+ d) = begin
  n div + d * + d        ≡⟨ cong (_* (+ d)) (div-pos-is-divℕ n d) ⟩
  n divℕ d  * + d        ≤⟨ [n/ℕd]*d≤n n d ⟩
  n                      ∎ where open ≤-Reasoning
[n/d]*d≤n n -[1+ d-1 ] = begin let d = ℕ.suc d-1 in
  n div (- + d) * - + d  ≡⟨ cong (_* (- + d)) (div-neg-is-neg-divℕ n d) ⟩
  - (n divℕ d)  * - + d  ≡⟨ sym (neg-distribˡ-* (n divℕ d) (- + d)) ⟩
  - (n divℕ d   * - + d) ≡⟨ neg-distribʳ-* (n divℕ d) (- + d) ⟩
  n divℕ d * + d         ≤⟨ [n/ℕd]*d≤n n d ⟩
  n                      ∎ where open ≤-Reasoning

n<s[n/ℕd]*d : ∀ n d .{{_ : ℕ.NonZero d}} → n ℤ.< suc (n divℕ d) ℤ.* ℤ.+ d
n<s[n/ℕd]*d n d = begin-strict
  n                    ≡⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  + r + q * + d        <⟨ +-monoˡ-< (q * + d) (ℤ.+<+ (n%ℕd<d n d)) ⟩
  + d + q * + d        ≡⟨ sym (suc-* q (+ d)) ⟩
  suc (n divℕ d) * + d ∎ where
  open ≤-Reasoning; q = n divℕ d; r = n modℕ d

a≡a%n+[a/n]*n : ∀ a n .{{_ : NonZero n}} → a ≡ + (a mod n) + (a div n) * n
a≡a%n+[a/n]*n n (+ d) = begin
  let r = n modℕ d; q = n divℕ d; qsd = q * + d in
  n                      ≡⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  + r + qsd              ≡⟨ cong (λ p → + r + p * + d) (sym (div-pos-is-divℕ n d)) ⟩
  + r + n div + d * + d  ∎ where open ≡-Reasoning
a≡a%n+[a/n]*n n -[1+ d ]    = begin
  let sd = ℕ.suc d; r = n modℕ sd; q = n divℕ sd; qsd = q * + sd in
  n                      ≡⟨ a≡a%ℕn+[a/ℕn]*n n sd ⟩
  + r + q * + sd         ≡⟨⟩
  + r + q * - -[1+ d ]   ≡⟨ cong (_+_ (+ r)) (sym (neg-distribʳ-* q -[1+ d ])) ⟩
  + r + - (q * -[1+ d ]) ≡⟨ cong (_+_ (+ r)) (neg-distribˡ-* q -[1+ d ]) ⟩
  + r + - q * -[1+ d ]   ≡⟨ cong (_+_ (+ r) ∘′ (_* -[1+ d ])) (sym (-1*i≡-i q)) ⟩
  + r + n div -[1+ d ] * -[1+ d ] ∎ where open ≡-Reasoning

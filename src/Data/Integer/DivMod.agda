------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Integer.DivMod where

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NProp
import Data.Nat.DivMod as NDM

import Data.Sign as S
import Data.Sign.Properties as SProp

open import Data.Integer as ℤ
open import Data.Integer.Properties

open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp

open import Function

open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

infixl 7 _divℕ_ _div_ _modℕ_ _mod_
_divℕ_ : (dividend : ℤ) (divisor : ℕ) {≢0 : False (divisor ℕ.≟ 0)} → ℤ
(+ n      divℕ d) {d≠0} = + (n NDM.div d) {d≠0}
(-[1+ n ] divℕ d) {d≠0} with (ℕ.suc n NDM.divMod d) {d≠0}
... | NDM.result q Fin.zero    eq = - (+ q)
... | NDM.result q (Fin.suc r) eq = -[1+ q ]

_div_ : (dividend divisor : ℤ) {≢0 : False (∣ divisor ∣ ℕ.≟ 0)} → ℤ
(n div d) {d≢0} = (sign d ◃ 1) ℤ.* (n divℕ ∣ d ∣) {d≢0}

_modℕ_ : (dividend : ℤ) (divisor : ℕ) {≠0 : False (divisor ℕ.≟ 0)} → ℕ
(+ n      modℕ d) {d≠0} = (n NDM.% d) {d≠0}
(-[1+ n ] modℕ d) {d≠0} with (ℕ.suc n NDM.divMod d) {d≠0}
... | NDM.result q Fin.zero    eq = 0
... | NDM.result q (Fin.suc r) eq = d ℕ.∸ ℕ.suc (Fin.toℕ r)

_mod_ : (dividend divisor : ℤ) {≠0 : False (∣ divisor ∣ ℕ.≟ 0)} → ℕ
(n mod d) {d≢0} = (n modℕ ∣ d ∣) {d≢0}

n%ℕd<d : ∀ n d {d≢0} → (n modℕ d) {d≢0} ℕ.< d
n%ℕd<d n ℕ.zero {()}
n%ℕd<d (+ n)    sd@(ℕ.suc d) = NDM.a%n<n n d
n%ℕd<d -[1+ n ] sd@(ℕ.suc d) with ℕ.suc n NDM.divMod sd
... | NDM.result q Fin.zero    eq = ℕ.s≤s ℕ.z≤n
... | NDM.result q (Fin.suc r) eq = ℕ.s≤s (NProp.n∸m≤n (Fin.toℕ r) d)

n%d<d : ∀ n d {d≢0} → (n mod d) {d≢0} ℕ.< ℤ.∣ d ∣
n%d<d n (+ 0) {()}
n%d<d n (+ ℕ.suc d) = n%ℕd<d n (ℕ.suc d)
n%d<d n -[1+ d ]    = n%ℕd<d n (ℕ.suc d)

a≡a%ℕn+[a/ℕn]*n : ∀ n d {d≢0} → n ≡ + (n modℕ d) {d≢0} + (n divℕ d) {d≢0} * + d
a≡a%ℕn+[a/ℕn]*n _ ℕ.zero {()}
a≡a%ℕn+[a/ℕn]*n (+ n) sd@(ℕ.suc d) = let q = n NDM.div sd; r = n NDM.% sd in begin
  + n                ≡⟨ cong +_ (NDM.a≡a%n+[a/n]*n n d) ⟩
  + (r ℕ.+ q ℕ.* sd) ≡⟨ pos-+-commute r (q ℕ.* sd) ⟩
  + r + + (q ℕ.* sd) ≡⟨ cong (_+_ (+ (+ n modℕ sd))) (sym (pos-distrib-* q sd)) ⟩
  + r + + q * + sd   ∎ where open ≡-Reasoning
a≡a%ℕn+[a/ℕn]*n -[1+ n ] sd@(ℕ.suc d) with (ℕ.suc n) NDM.divMod (ℕ.suc d)
... | NDM.result q Fin.zero    eq = begin
  -[1+ n ]            ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (q ℕ.* sd)      ≡⟨ cong -_ (sym (pos-distrib-* q sd)) ⟩
  - (+ q * + sd)      ≡⟨ neg-distribˡ-* (+ q) (+ sd) ⟩
  - (+ q) * + sd      ≡⟨ sym (+-identityˡ (- (+ q) * + sd)) ⟩
  + 0 + - (+ q) * + sd ∎ where open ≡-Reasoning
... | NDM.result q (Fin.suc r) eq = begin
  let sd = ℕ.suc d; sr = ℕ.suc (Fin.toℕ r); sq = ℕ.suc q in
  -[1+ n ]
    ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (sr ℕ.+ q ℕ.* sd)
    ≡⟨ cong -_ (pos-+-commute sr (q ℕ.* sd)) ⟩
  - (+ sr + + (q ℕ.* sd))
    ≡⟨ neg-distrib-+ (+ sr) (+ (q ℕ.* sd)) ⟩
  - + sr - + (q ℕ.* sd)
    ≡⟨ cong (_-_ (- + sr)) (sym (pos-distrib-* q sd)) ⟩
  - + sr - (+ q) * (+ sd)
    ≡⟨⟩
  - + sr - pred (+ sq) * (+ sd)
    ≡⟨ cong (_-_ (- + sr)) (*-distribʳ-+ (+ sd) (- + 1)  (+ sq)) ⟩
  - + sr - (- (+ 1) * + sd + (+ sq * + sd))
    ≡⟨ cong (_+_ (- (+ sr))) (neg-distrib-+ (- (+ 1) * + sd) (+ sq * + sd)) ⟩
  - + sr + (- (-[1+ 0 ] * + sd) + - (+ sq * + sd))
    ≡⟨ cong₂ (λ p q → - + sr + (- p + q)) (-1*n≡-n (+ sd))
                                            (neg-distribˡ-* (+ sq) (+ sd)) ⟩
  - + sr + ((- - + sd) + -[1+ q ] * + sd)
    ≡⟨ sym (+-assoc (- + sr) (- - + sd) (-[1+ q ] * + sd)) ⟩
  (+ sd - + sr) + -[1+ q ] * + sd
    ≡⟨ cong (_+ -[1+ q ] * + sd) (fin-inv d r) ⟩
  + (sd ℕ.∸ sr) + -[1+ q ] * + sd
    ∎ where

    open ≡-Reasoning

    fin-inv : ∀ d (k : Fin d) → + (ℕ.suc d) - + ℕ.suc (Fin.toℕ k) ≡ + (d ℕ.∸ Fin.toℕ k)
    fin-inv (ℕ.suc n) Fin.zero    = refl
    fin-inv (ℕ.suc n) (Fin.suc k) = ⊖-≥ {n} {Fin.toℕ k} (NProp.<⇒≤ (FProp.toℕ<n k))

[n/ℕd]*d≤n : ∀ n d {d≢0} → (n divℕ d) {d≢0} ℤ.* ℤ.+ d ℤ.≤ n
[n/ℕd]*d≤n n ℕ.zero {()}
[n/ℕd]*d≤n n (ℕ.suc d) = let q = n divℕ ℕ.suc d; r = n modℕ ℕ.suc d in begin
  q ℤ.* ℤ.+ (ℕ.suc d)           ≤⟨ n≤m+n r ⟩
  ℤ.+ r ℤ.+ q ℤ.* ℤ.+ (ℕ.suc d) ≡⟨ sym (a≡a%ℕn+[a/ℕn]*n n (ℕ.suc d)) ⟩
  n                             ∎ where open ≤-Reasoning

div-pos-is-divℕ : ∀ n d {d≢0} → (n div + d) {d≢0} ≡ (n divℕ d) {d≢0}
div-pos-is-divℕ n ℕ.zero {()}
div-pos-is-divℕ n (ℕ.suc d) = *-identityˡ (n divℕ ℕ.suc d)

div-neg-is-neg-divℕ : ∀ n d {d≢0} {∣d∣≢0} → (n div (- ℤ.+ d)) {∣d∣≢0} ≡ - (n divℕ d) {d≢0}
div-neg-is-neg-divℕ n ℕ.zero {()}
div-neg-is-neg-divℕ n (ℕ.suc d) = -1*n≡-n (n divℕ ℕ.suc d)

0≤n⇒0≤n/ℕd : ∀ n d {d≢0} → + 0 ℤ.≤ n → + 0 ℤ.≤ (n divℕ d) {d≢0}
0≤n⇒0≤n/ℕd (+ n) d (+≤+ m≤n) = +≤+ ℕ.z≤n

0≤n⇒0≤n/d : ∀ n d {d≢0} → + 0 ℤ.≤ n → + 0 ℤ.≤ d → + 0 ℤ.≤ (n div d) {d≢0}
0≤n⇒0≤n/d n (+ d) {d≢0} 0≤n (+≤+ 0≤d)
  rewrite div-pos-is-divℕ n d {d≢0}
        = 0≤n⇒0≤n/ℕd n d 0≤n

[n/d]*d≤n : ∀ n d {d≢0} → (n div d) {d≢0} ℤ.* d ℤ.≤ n
[n/d]*d≤n n (+ 0) {()}
[n/d]*d≤n n (+ ℕ.suc d) = begin let sd = ℕ.suc d in
  n div + sd * + sd ≡⟨ cong (_* (+ sd)) (div-pos-is-divℕ n sd) ⟩
  n divℕ sd * + sd  ≤⟨ [n/ℕd]*d≤n n sd ⟩
  n ∎ where open ≤-Reasoning
[n/d]*d≤n n -[1+ d ]    = begin let sd = ℕ.suc d in
  n div (- + sd) * - + sd ≡⟨ cong (_* (- + sd)) (div-neg-is-neg-divℕ n sd) ⟩
  - (n divℕ sd) * - + sd  ≡⟨ sym (neg-distribˡ-* (n divℕ sd) (- + sd)) ⟩
  - (n divℕ sd * - + sd)  ≡⟨ neg-distribʳ-* (n divℕ sd) (- + sd) ⟩
  n divℕ sd * + sd        ≤⟨ [n/ℕd]*d≤n n sd ⟩
  n ∎ where open ≤-Reasoning

n<s[n/ℕd]*d : ∀ n d {d≢0} → n ℤ.< ℤ.suc ((n divℕ d) {d≢0}) ℤ.* ℤ.+ d
n<s[n/ℕd]*d n ℕ.zero {()}
n<s[n/ℕd]*d n sd@(ℕ.suc d) = begin
  suc n                     ≡⟨ cong suc (a≡a%ℕn+[a/ℕn]*n n sd) ⟩
  suc (ℤ.+ r ℤ.+ q ℤ.* +sd) ≤⟨ +-monoˡ-< (q ℤ.* +sd) {ℤ.+ r} (ℤ.+≤+ (n%ℕd<d n sd)) ⟩
  +sd ℤ.+ q ℤ.* +sd         ≡⟨ sym (sm*n≡n+m*n q +sd) ⟩
  ℤ.suc q ℤ.* +sd           ∎ where
  q = n divℕ sd; +sd = ℤ.+ sd; r = n modℕ sd
  open ≤-Reasoning

a≡a%n+[a/n]*n : ∀ a n {≢0} → a ≡ + (a mod n) {≢0} + (a div n) {≢0} * n
a≡a%n+[a/n]*n n (+ 0) {()}
a≡a%n+[a/n]*n n (+ ℕ.suc d) = begin
  let sd = ℕ.suc d; r = n modℕ sd; q = n divℕ sd; qsd = q * + sd in
  n                       ≡⟨ a≡a%ℕn+[a/ℕn]*n n sd ⟩
  + r + qsd               ≡⟨ cong (λ p → + r + p * + sd) (sym (div-pos-is-divℕ n sd)) ⟩
  + r + n div + sd * + sd ∎ where open ≡-Reasoning
a≡a%n+[a/n]*n n -[1+ d ]    = begin
  let sd = ℕ.suc d; r = n modℕ sd; q = n divℕ sd; qsd = q * + sd in
  n                      ≡⟨ a≡a%ℕn+[a/ℕn]*n n sd ⟩
  + r + q * + sd         ≡⟨⟩
  + r + q * - -[1+ d ]   ≡⟨ cong (_+_ (+ r)) (sym (neg-distribʳ-* q -[1+ d ])) ⟩
  + r + - (q * -[1+ d ]) ≡⟨ cong (_+_ (+ r)) (neg-distribˡ-* q -[1+ d ]) ⟩
  + r + - q * -[1+ d ]   ≡⟨ cong (_+_ (+ r) ∘′ (_* -[1+ d ])) (sym (-1*n≡-n q)) ⟩
  + r + n div -[1+ d ] * -[1+ d ] ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.DivMod where

open import Data.Integer.Base
open import Data.Integer.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; z<s; s<s)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as ℕ
import Data.Sign as S
open import Function.Base using (_∘′_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition

open import Data.Integer.Base public
  using (_/ℕ_; _/_; _%ℕ_; _%_)

------------------------------------------------------------------------
-- Properties

n%ℕd<d : ∀ n d .{{_ : ℕ.NonZero d}} → n %ℕ d ℕ.< d
n%ℕd<d (+ n)    d           = ℕ.m%n<n n d
n%ℕd<d -[1+ n ] d@(ℕ.suc _) with ℕ.suc n ℕ.% d
... | ℕ.zero  = z<s
... | ℕ.suc r = s<s (ℕ.m∸n≤m _ r)

n%d<d : ∀ n d .{{_ : NonZero d}} → n % d ℕ.< ∣ d ∣
n%d<d n (+ d)    = n%ℕd<d n d
n%d<d n -[1+ d ] = n%ℕd<d n (ℕ.suc d)

a≡a%ℕn+[a/ℕn]*n : ∀ n d .{{_ : ℕ.NonZero d}} → n ≡ + (n %ℕ d) + (n /ℕ d) * + d
a≡a%ℕn+[a/ℕn]*n (+ n) d = let q = n ℕ./ d; r = n ℕ.% d in begin-equality
  + n                ≡⟨ cong +_ (ℕ.m≡m%n+[m/n]*n n d) ⟩
  + (r ℕ.+ q ℕ.* d)  ≡⟨ pos-+ r (q ℕ.* d) ⟩
  + r + + (q ℕ.* d)  ≡⟨ cong (_+_ (+ r)) (pos-* q d) ⟩
  + r + + q * + d    ∎
a≡a%ℕn+[a/ℕn]*n n@(-[1+ _ ]) d with ∣ n ∣ ℕ.% d in eq
... | ℕ.zero = begin-equality
  n                   ≡⟨ cong (-_ ∘′ +_) (ℕ.m≡m%n+[m/n]*n ∣n∣ d) ⟩
  - + (r ℕ.+ q ℕ.* d) ≡⟨ cong (-_ ∘′ +_) (cong (ℕ._+ q ℕ.* d) eq) ⟩
  - + (q ℕ.* d)       ≡⟨ cong -_ (pos-* q d) ⟩
  - (+ q * + d)       ≡⟨ neg-distribˡ-* (+ q) (+ d) ⟩
  - (+ q) * + d       ≡⟨ sym (+-identityˡ (- (+ q) * + d)) ⟩
  + 0 + - (+ q) * + d ∎
  where ∣n∣ = ∣ n ∣; q = ∣n∣ ℕ./ d; r = ∣n∣ ℕ.% d
... | r@(ℕ.suc _) = begin-equality
  let ∣n∣ = ∣ n ∣; q = ∣n∣ ℕ./ d; r′ = ∣n∣ ℕ.% d in
  n                                      ≡⟨ cong (-_ ∘′ +_) (ℕ.m≡m%n+[m/n]*n ∣n∣ d) ⟩
  - + (r′ ℕ.+ q ℕ.* d)                   ≡⟨ cong (-_ ∘′ +_) (cong (ℕ._+ q ℕ.* d) eq) ⟩
  - + (r  ℕ.+ q ℕ.* d)                   ≡⟨ cong -_ (pos-+ r (q ℕ.* d)) ⟩
  - (+ r + + (q ℕ.* d))                  ≡⟨ neg-distrib-+ (+ r) (+ (q ℕ.* d)) ⟩
  - + r - + (q ℕ.* d)                    ≡⟨ cong (_-_ (- + r)) (pos-* q d) ⟩
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

[n/ℕd]*d≤n : ∀ n d .{{_ : ℕ.NonZero d}} → (n /ℕ d) * + d ≤ n
[n/ℕd]*d≤n n d = let q = n /ℕ d; r = n %ℕ d in begin
  q * + d        ≤⟨  i≤j+i _ (+ r) ⟩
  + r + q * + d  ≡˘⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  n              ∎

div-pos-is-/ℕ : ∀ n d .{{_ : ℕ.NonZero d}} →
                  n / (+ d) ≡ n /ℕ d
div-pos-is-/ℕ n (ℕ.suc d) = *-identityˡ (n /ℕ ℕ.suc d)

div-neg-is-neg-/ℕ : ∀ n d .{{_ : ℕ.NonZero d}} .{{_ : NonZero (- + d)}} →
                      n / (- + d) ≡ - (n /ℕ d)
div-neg-is-neg-/ℕ n (ℕ.suc d) = -1*i≡-i (n /ℕ ℕ.suc d)

0≤n⇒0≤n/ℕd : ∀ n d .{{_ : ℕ.NonZero d}} → 0ℤ ≤ n → 0ℤ ≤ (n /ℕ d)
0≤n⇒0≤n/ℕd (+ n) d (+≤+ m≤n) = +≤+ z≤n

0≤n⇒0≤n/d : ∀ n d .{{_ : NonZero d}} → 0ℤ ≤ n → 0ℤ ≤ d → 0ℤ ≤ (n / d)
0≤n⇒0≤n/d n (+ d) {{d≢0}} 0≤n (+≤+ 0≤d)
  rewrite div-pos-is-/ℕ n d {{d≢0}}
        = 0≤n⇒0≤n/ℕd n d 0≤n

[n/d]*d≤n : ∀ n d .{{_ : NonZero d}} → (n / d) * d ≤ n
[n/d]*d≤n n (+ d) = begin
  n / + d * + d        ≡⟨ cong (_* (+ d)) (div-pos-is-/ℕ n d) ⟩
  n /ℕ d  * + d        ≤⟨ [n/ℕd]*d≤n n d ⟩
  n                    ∎
[n/d]*d≤n n d@(-[1+ _ ]) = begin let ∣d∣ = ∣ d ∣ in
  n / d        * d     ≡⟨ cong (_* d) (div-neg-is-neg-/ℕ n ∣d∣) ⟩
  - (n /ℕ ∣d∣) * d     ≡⟨ sym (neg-distribˡ-* (n /ℕ ∣d∣) d) ⟩
  - (n /ℕ ∣d∣  * d)    ≡⟨ neg-distribʳ-* (n /ℕ ∣d∣) d ⟩
  n /ℕ ∣d∣     * + ∣d∣ ≤⟨ [n/ℕd]*d≤n n ∣d∣ ⟩
  n                    ∎

n<s[n/ℕd]*d : ∀ n d .{{_ : ℕ.NonZero d}} → n < suc (n /ℕ d) * + d
n<s[n/ℕd]*d n d = begin-strict
  n                    ≡⟨ a≡a%ℕn+[a/ℕn]*n n d ⟩
  + r + q * + d        <⟨ +-monoˡ-< (q * + d) (+<+ (n%ℕd<d n d)) ⟩
  + d + q * + d        ≡⟨ sym (suc-* q (+ d)) ⟩
  suc (n /ℕ d) * + d   ∎
  where q = n /ℕ d; r = n %ℕ d

a≡a%n+[a/n]*n : ∀ a n .{{_ : NonZero n}} → a ≡ + (a % n) + (a / n) * n
a≡a%n+[a/n]*n n d@(+ _) = begin-equality
  let ∣d∣ = ∣ d ∣; r = n % d; q = n /ℕ ∣d∣ in
  n                  ≡⟨ a≡a%ℕn+[a/ℕn]*n n ∣d∣ ⟩
  + r + (q * + ∣d∣)  ≡⟨ cong (λ p → + r + p * d) (sym (div-pos-is-/ℕ n ∣d∣)) ⟩
  + r + n / d * d    ∎
a≡a%n+[a/n]*n n d@(-[1+ _ ]) = begin-equality
  let ∣d∣ = ∣ d ∣; r = n % d; q = n /ℕ ∣d∣ in
  n                  ≡⟨ a≡a%ℕn+[a/ℕn]*n n ∣d∣ ⟩
  + r + q * + ∣d∣    ≡⟨⟩
  + r + q * - d      ≡⟨ cong (_+_ (+ r)) (sym (neg-distribʳ-* q d)) ⟩
  + r + - (q * d)    ≡⟨ cong (_+_ (+ r)) (neg-distribˡ-* q d) ⟩
  + r + - q * d      ≡⟨ cong (_+_ (+ r) ∘′ (_* d)) (sym (-1*i≡-i q)) ⟩
  + r + n / d * d    ∎

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

infixl 7 _divℕ_ _div_ _modℕ_ _mod_
_divℕ_ = _/ℕ_
{-# WARNING_ON_USAGE _divℕ_
"Warning: _divℕ_ was deprecated in v2.0.
Please use _/ℕ_ instead."
#-}
_div_ = _/_
{-# WARNING_ON_USAGE _div_
"Warning: _div_ was deprecated in v2.0.
Please use _/_ instead."
#-}
_modℕ_ = _%ℕ_
{-# WARNING_ON_USAGE _modℕ_
"Warning: _modℕ_ was deprecated in v2.0.
Please use _%ℕ_ instead."
#-}
_mod_ = _%_
{-# WARNING_ON_USAGE _mod_
"Warning: _mod_ was deprecated in v2.0.
Please use _%_ instead."
#-}

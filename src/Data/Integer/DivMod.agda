------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.DivMod where

open import Data.Integer.Base
open import Data.Integer.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; z<s; s<s)
import Data.Nat.DivMod as ℕ using (m≡m%n+[m/n]*n; m%n≤n; m%n<n; n/1≡n; n%1≡0;
  m*n/m*o≡n/o; m*n%o≡m*n%[m*o])
import Data.Nat.Properties as ℕ using (m∸n≤m; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0;
  m*n≡0⇒n≡0; *-comm)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; sym; subst; trans; respʳ)
open import Relation.Nullary.Negation using (contradiction)
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
  + r + q * + d  ≡⟨ a≡a%ℕn+[a/ℕn]*n n d ⟨
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

i/ℕ1≡i : ∀ i → i /ℕ 1 ≡ i
i/ℕ1≡i (+ n) = cong +_ (ℕ.n/1≡n n)
i/ℕ1≡i -[1+ n ] with ℕ.suc n ℕ.% 1 | ℕ.n%1≡0 (ℕ.suc n)
... | ℕ.zero | suc[n]%1≡0 = cong (λ x → - (+ x)) (ℕ.n/1≡n (ℕ.suc n))

i/1≡i : ∀ i → i / + 1 ≡ i
i/1≡i i = trans (div-pos-is-/ℕ i 1) (i/ℕ1≡i i)

/ℕ-congʳ : ∀ i {m} {n} .{{_ : ℕ.NonZero m}} → .{{_ : ℕ.NonZero n}} →
           m ≡ n → i /ℕ m ≡ i /ℕ n
/ℕ-congʳ i {m} {n} refl = refl

nonNeg[i]⇒i/ℕd : ∀ i d .{{_ : ℕ.NonZero d}} .{{_ : NonNegative i}} →
                i /ℕ d ≡ + (∣ i ∣ ℕ./ d)
nonNeg[i]⇒i/ℕd (+ i) d = refl

neg[i]∧∣i∣%d≡0⇒i/ℕd : ∀ i {d} .{{_ : ℕ.NonZero d}} .{{_ : Negative i}} →
                     ∣ i ∣ ℕ.% d ≡ 0 → i /ℕ d ≡ - (+ (∣ i ∣ ℕ./ d))
neg[i]∧∣i∣%d≡0⇒i/ℕd -[1+ n ] {d} _ with ℕ.zero ← ℕ.suc n ℕ.% d = refl

neg[i]∧∣i∣%d≢0⇒i/ℕd : ∀ i d .{{_ : ℕ.NonZero d}} .{{_ : Negative i}}
                     .{{_ : ℕ.NonZero (∣ i ∣ ℕ.% d)}} → i /ℕ d ≡ -[1+ ∣ i ∣ ℕ./ d ]
neg[i]∧∣i∣%d≢0⇒i/ℕd -[1+ n ] d {{_}} {{_}} {{mod}} with ℕ.suc n ℕ.% d
... | ℕ.zero  = contradiction refl (ℕ.≢-nonZero⁻¹ ℕ.zero)
... | ℕ.suc _ = refl

*-cancelˡ-/ℕ : ∀ m i n .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero (m ℕ.* n)}} →
               (+ m * i) /ℕ (m ℕ.* n) ≡ i /ℕ n
*-cancelˡ-/ℕ m i@(+ _) n = begin-equality
  (+ m * i) /ℕ (m ℕ.* n)
      ≡⟨ nonNeg[i]⇒i/ℕd (+ m * i) (m ℕ.* n) ⟩
  + (∣ + m * i ∣ ℕ./ (m ℕ.* n))
      ≡⟨ cong (+_ ∘′ (ℕ._/ (m ℕ.* n))) (∣i*j∣≡∣i∣*∣j∣ (+ m) i) ⟩
  + ((m ℕ.* ∣ i ∣) ℕ./ (m ℕ.* n))
      ≡⟨ cong +_ (ℕ.m*n/m*o≡n/o m ∣ i ∣ n) ⟩
  + (∣ i ∣ ℕ./ n)
      ≡⟨ nonNeg[i]⇒i/ℕd i n ⟨
  i /ℕ n ∎
  where
    instance
      _ : ℕ.NonZero m
      _ = ℕ.m*n≢0⇒m≢0 m
      _ : NonNegative (+ m * i)
      _ = i≥0∧j≥0⇒i*j≥0 (+ m) i
*-cancelˡ-/ℕ m i@(-[1+ _ ]) n = helper
  where
    m*[∣i∣%n]≡∣m*i∣%[m*n] : m ℕ.* (∣ i ∣ ℕ.% n) ≡ ∣ + m * i ∣ ℕ.% (m ℕ.* n)
    m*[∣i∣%n]≡∣m*i∣%[m*n] = trans (ℕ.m*n%o≡m*n%[m*o] m ∣ i ∣ n)
                                  (cong (ℕ._% (m ℕ.* n)) (sym (∣i*j∣≡∣i∣*∣j∣ (+ m) i)))
    instance
      _ : ℕ.NonZero m
      _ = ℕ.m*n≢0⇒m≢0 m
      _ : Positive (+ m)
      _ = nonNeg∧nonZero⇒Pos (+ m)
      _ : Negative (+ m * i)
      _ = i>0∧j<0⇒i*j<0 (+ m) i
    helper : (+ m * i) /ℕ (m ℕ.* n) ≡ i /ℕ n
    helper with ∣ + m * i ∣ ℕ.% (m ℕ.* n) in ∣m*i∣%[m*n]
    ... | ℕ.zero = begin-equality
      (+ m * i) /ℕ (m ℕ.* n)
          ≡⟨ neg[i]∧∣i∣%d≡0⇒i/ℕd (+ m * i) ∣m*i∣%[m*n] ⟩
      - (+ (∣ + m * i ∣ ℕ./ (m ℕ.* n)))
          ≡⟨ cong (-_ ∘′ +_ ∘′ (ℕ._/ _)) (∣i*j∣≡∣i∣*∣j∣ (+ m) i) ⟩
      - (+ ((m ℕ.* ∣ i ∣) ℕ./ (m ℕ.* n)))
          ≡⟨ cong (-_ ∘′ +_) (ℕ.m*n/m*o≡n/o m ∣ i ∣ n) ⟩
      - (+ (∣ i ∣ ℕ./ n)) ≡⟨ neg[i]∧∣i∣%d≡0⇒i/ℕd i ∣i∣%m≡0 ⟨
      i /ℕ n ∎
      where
        m*[∣i∣%n]≡0 : m ℕ.* (∣ i ∣ ℕ.% n) ≡ 0
        m*[∣i∣%n]≡0 = trans m*[∣i∣%n]≡∣m*i∣%[m*n] ∣m*i∣%[m*n]
        ∣i∣%m≡0 : ∣ i ∣ ℕ.% n ≡ 0
        ∣i∣%m≡0 = ℕ.m*n≡0⇒n≡0 m _ m*[∣i∣%n]≡0
    ... | ℕ.suc _ = begin-equality
      (+ m * i) /ℕ (m ℕ.* n)
          ≡⟨ neg[i]∧∣i∣%d≢0⇒i/ℕd (+ m * i) (m ℕ.* n) ⟩
      -[1+ ∣ + m * i ∣ ℕ./ (m ℕ.* n) ]
          ≡⟨ cong (-[1+_] ∘′ (ℕ._/ (m ℕ.* n))) (∣i*j∣≡∣i∣*∣j∣ (+ m) i) ⟩
      -[1+ (m ℕ.* ∣ i ∣) ℕ./ (m ℕ.* n) ]
          ≡⟨ cong -[1+_] (ℕ.m*n/m*o≡n/o m ∣ i ∣ n) ⟩
      -[1+ ∣ i ∣ ℕ./ n ] ≡⟨ neg[i]∧∣i∣%d≢0⇒i/ℕd i n ⟨
      i /ℕ n ∎
      where instance
        ∣m*i∣%[m*n]≢0 : ℕ.NonZero (∣ + m * i ∣ ℕ.% (m ℕ.* n))
        ∣m*i∣%[m*n]≢0 rewrite ∣m*i∣%[m*n] = _
        m*[∣i∣%n]≢0 : ℕ.NonZero (m ℕ.* (∣ i ∣ ℕ.% n))
        m*[∣i∣%n]≢0 rewrite m*[∣i∣%n]≡∣m*i∣%[m*n] | ∣m*i∣%[m*n] = _
        ∣i∣%n≢0 : ℕ.NonZero (∣ i ∣ ℕ.% n)
        ∣i∣%n≢0 = ℕ.m*n≢0⇒n≢0 m

*-cancelʳ-/ℕ : ∀ i m n .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero (n ℕ.* m)}} →
               (i * + m) /ℕ (n ℕ.* m) ≡ i /ℕ n
*-cancelʳ-/ℕ i m n rewrite *-comm i (+ m) | ℕ.*-comm n m = *-cancelˡ-/ℕ m i n

*-cancelˡ-/ : ∀ i j k .{{_ : NonZero k}} .{{_ : NonZero (i * k)}} →
              .{{_ : NonNegative i}} → (i * j) / (i * k) ≡ j / k
*-cancelˡ-/ (+ i) j k = begin-equality
  (sign (+ i * k) ◃ 1) * ((+ i * j) /ℕ ∣ + i * k ∣)
        ≡⟨ cong (λ x → (x ◃ 1) * ((+ i * j) /ℕ _)) (sign-* (+ i) k)⟩
  (sign k ◃ 1) * ((+ i * j) /ℕ ∣ + i * k ∣)
        ≡⟨ cong ((sign k ◃ 1) *_) (/ℕ-congʳ (+ i * j) (∣i*j∣≡∣i∣*∣j∣ (+ i) k)) ⟩
  (sign k ◃ 1) * ((+ i * j) /ℕ (∣ + i ∣ ℕ.* ∣ k ∣))
        ≡⟨ cong ((sign k ◃ 1) *_) (*-cancelˡ-/ℕ i j ∣ k ∣) ⟩
  j / k ∎
  where
    instance
      _ : NonZero (+ i)
      _ = i*j≢0⇒i≢0 (+ i)
      _ : ℕ.NonZero (∣ + i ∣ ℕ.* ∣ k ∣)
      _ = ℕ.m*n≢0 ∣ + i ∣ ∣ k ∣

*-cancelʳ-/ : ∀ i j k .{{_ : NonZero k}} .{{_ : NonZero (k * j)}} →
              .{{_ : NonNegative j}} → (i * j) / (k * j) ≡ i / k
*-cancelʳ-/ i j k rewrite *-comm i j | *-comm k j = *-cancelˡ-/ j i k

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

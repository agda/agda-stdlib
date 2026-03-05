------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.DivMod where

open import Data.Integer.Base using (+_; -[1+_]; +[1+_]; ∣_∣; _+_; _*_; -_;
  _-_; suc; pred; -1ℤ; 0ℤ; _⊖_; _≤_; _≥_; _<_; +≤+; -≤-; -≤+; +<+; -<+;
  NonZero; NonNegative; NonPositive; Negative; Positive)
open import Data.Integer.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; z<s; s<s)
import Data.Nat.Properties as ℕ using (≤-reflexive; m∸n≤m; m<n⇒0<n)
import Data.Nat.DivMod as ℕ using (m≡m%n+[m/n]*n; m%n≤n; m%n<n; n/1≡n; n%1≡0;
  m/n≡0⇒m<n; m<n⇒m/n≡0; sn%d≡0⇒sn/d≡s[n/d]; sn%d>0⇒sn/d≡n/d; /-monoˡ-≤;
  /-monoʳ-≤; 0/n≡0)
open import Function.Base using (_∘′_)
open import Relation.Binary.Definitions using (Monotonic₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; subst; trans)
open import Relation.Nullary.Negation.Core using (contradiction)

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

n<0⇒n/ℕd<0 : ∀ n d .{{_ : ℕ.NonZero d}} → n < 0ℤ → (n /ℕ d) < 0ℤ
n<0⇒n/ℕd<0 -[1+ n ] d -<+
  with ℕ.suc n ℕ.% d in sn%d
... | ℕ.zero  = begin-strict
  - (+ (ℕ.suc n ℕ./ d))   ≡⟨ cong (-_ ∘′ +_) (ℕ.sn%d≡0⇒sn/d≡s[n/d] n d sn%d) ⟩
  - (+ (ℕ.suc (n ℕ./ d))) <⟨ -<+ ⟩
  + 0                     ∎
... | ℕ.suc _ = -<+

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

0/ℕd≡0 : ∀ d .{{_ : ℕ.NonZero d}} → + 0 /ℕ d ≡ + 0
0/ℕd≡0 d = cong (+_) (ℕ.0/n≡0 d)

0/d≡0 : ∀ d .{{_ : NonZero d}} → + 0 / d ≡ + 0
0/d≡0 (+ d) = trans (div-pos-is-/ℕ (+ 0) d) (0/ℕd≡0 d)
0/d≡0 -[1+ d ] = trans (div-neg-is-neg-/ℕ (+ 0) (ℕ.suc d))
                       (cong (-_) (0/ℕd≡0 (ℕ.suc d)))

n/ℕ1≡n : ∀ n → n /ℕ 1 ≡ n
n/ℕ1≡n (+ n) = cong +_ (ℕ.n/1≡n n)
n/ℕ1≡n -[1+ n ] rewrite ℕ.n%1≡0 (ℕ.suc n) = cong (-_ ∘′ +_) (ℕ.n/1≡n (ℕ.suc n))

n/1≡n : ∀ n → n / + 1 ≡ n
n/1≡n n = trans (div-pos-is-/ℕ n 1) (n/ℕ1≡n n)

n/ℕd≡0⇒∣n∣<d : ∀ n d .{{_ : ℕ.NonZero d}} → n /ℕ d ≡ 0ℤ → ∣ n ∣ ℕ.< d
n/ℕd≡0⇒∣n∣<d (+ n) d _ with ℕ.zero ← n ℕ./ d in n/d≡0 = ℕ.m/n≡0⇒m<n n/d≡0
n/ℕd≡0⇒∣n∣<d (-[1+ n ]) d n/ℕd≡0 with ℕ.zero ← ℕ.suc n ℕ.% d
    | ℕ.suc n ℕ./ d in n/d
... | ℕ.zero  = ℕ.m/n≡0⇒m<n n/d
... | ℕ.suc _ = contradiction n/ℕd≡0 λ ()

0≤n<d⇒n/ℕd≡0 : ∀ n d .{{_ : NonNegative n }} .{{_ : ℕ.NonZero d}} →
                n < + d → n /ℕ d ≡ 0ℤ
0≤n<d⇒n/ℕd≡0 (+ n) d (+<+ n<d) = cong (+_) (ℕ.m<n⇒m/n≡0 n<d)

n/d≡0⇒∣n∣<∣d∣ : ∀ n d .{{_ : NonZero d}} → n / d ≡ 0ℤ → ∣ n ∣ ℕ.< ∣ d ∣
n/d≡0⇒∣n∣<∣d∣ n (+ d) n/d≡0ℤ =
              n/ℕd≡0⇒∣n∣<d n d (trans (sym (div-pos-is-/ℕ n d)) n/d≡0ℤ)
n/d≡0⇒∣n∣<∣d∣ n -[1+ d ] n/d≡0ℤ =
              n/ℕd≡0⇒∣n∣<d n (ℕ.suc d) (neg-injective {_} {+ 0}
                (trans (sym (div-neg-is-neg-/ℕ n (ℕ.suc d))) n/d≡0ℤ))

0≤n<∣d∣⇒n/d≡0 : ∀ n d .{{_ : NonNegative n }} .{{_ : NonZero d}} →
                n < + ∣ d ∣ → n / d ≡ 0ℤ
0≤n<∣d∣⇒n/d≡0 n (+ d) (+<+ n<d) = begin-equality
  n / + d ≡⟨ div-pos-is-/ℕ n d ⟩
  n /ℕ d  ≡⟨ (0≤n<d⇒n/ℕd≡0 n d (+<+ n<d)) ⟩
  0ℤ ∎
0≤n<∣d∣⇒n/d≡0 n -[1+ d ] (+<+ n<d) = begin-equality
  n / -[1+ d ]     ≡⟨ div-neg-is-neg-/ℕ n (ℕ.suc d) ⟩
  - (n /ℕ ℕ.suc d) ≡⟨ cong (-_) (0≤n<d⇒n/ℕd≡0 n (ℕ.suc d) (+<+ n<d)) ⟩
  - 0ℤ ∎

private
  /ℕ-monoˡ-≤-pos-pos : ∀ n m d .{{_ : NonNegative n}} .{{_ : NonNegative m}}
                       .{{_ : ℕ.NonZero d}} → n ≤ m → n /ℕ d ≤ m /ℕ d
  /ℕ-monoˡ-≤-pos-pos _ _ d (+≤+ n≤m) = +≤+ (ℕ./-monoˡ-≤ d n≤m)

  /ℕ-monoˡ-≤-neg-pos : ∀ n m d .{{_ : Negative n}} .{{_ : NonNegative m}}
                       .{{_ : ℕ.NonZero d}} → n ≤ m → n /ℕ d ≤ m /ℕ d
  /ℕ-monoˡ-≤-neg-pos n@(-[1+ _ ]) m@(+ _) d -≤+ =
    <⇒≤ (<-≤-trans (n<0⇒n/ℕd<0 n d -<+) (0≤n⇒0≤n/ℕd m d (+≤+ z≤n)))

  n≡sk>0 : ∀ {n k} → n ≡ ℕ.suc k → 0 ℕ.< n
  n≡sk>0 n≡sk = ℕ.m<n⇒0<n (ℕ.≤-reflexive (sym n≡sk))

  /ℕ-monoˡ-≤-neg-neg : ∀ n m d .{{_ : Negative n}} .{{_ : Negative m}}
                       .{{_ : ℕ.NonZero d}} → n ≤ m → n /ℕ d ≤ m /ℕ d
  /ℕ-monoˡ-≤-neg-neg (-[1+ n ]) (-[1+ m ]) d (-≤- m≤n)
    with ℕ.suc n ℕ.% d in sn%d | ℕ.suc m ℕ.% d in sm%d
  ... | ℕ.zero | ℕ.zero  = neg-mono-≤ (+≤+ (ℕ./-monoˡ-≤ d (s≤s m≤n)))
  ... | ℕ.zero | ℕ.suc _ = let sm%d>0 = n≡sk>0 sm%d in begin
    -(+(ℕ.suc n ℕ./ d))   ≡⟨ cong (-_ ∘′ +_) (ℕ.sn%d≡0⇒sn/d≡s[n/d] n d sn%d) ⟩
    -[1+ n ℕ./ d ]        ≤⟨ -≤- (ℕ./-monoˡ-≤ d m≤n) ⟩
    -[1+ m ℕ./ d ]        ≡⟨ cong -[1+_] (ℕ.sn%d>0⇒sn/d≡n/d m d sm%d>0)⟨
    -[1+ ℕ.suc m ℕ./ d ]  ∎
  ... | ℕ.suc _ | ℕ.zero  = let sn%d>0 = n≡sk>0 sn%d in begin
    -[1+ ℕ.suc n ℕ./ d ]  ≡⟨ cong -[1+_] (ℕ.sn%d>0⇒sn/d≡n/d n d sn%d>0)⟩
    -[1+ n ℕ./ d ]        ≤⟨ -≤- (ℕ./-monoˡ-≤ d m≤n) ⟩
    -(+(ℕ.suc (m ℕ./ d))) ≡⟨ cong (-_ ∘′ +_) (ℕ.sn%d≡0⇒sn/d≡s[n/d] m d sm%d) ⟨
    -(+(ℕ.suc m ℕ./ d))   ∎
  ... | ℕ.suc _ | ℕ.suc _ = -≤- (ℕ./-monoˡ-≤ d (s≤s m≤n))

/ℕ-monoˡ-≤ : ∀ d .{{_ : ℕ.NonZero d}} → Monotonic₁ _≤_ _≤_ (_/ℕ d)
/ℕ-monoˡ-≤ d {n@(+ _)}      {m@(+ _)}      n≤m = /ℕ-monoˡ-≤-pos-pos n m d n≤m
/ℕ-monoˡ-≤ d {n@(-[1+ _ ])} {m@(+ _)}      n≤m = /ℕ-monoˡ-≤-neg-pos n m d n≤m
/ℕ-monoˡ-≤ d {n@(-[1+ _ ])} {m@(-[1+ _ ])} n≤m = /ℕ-monoˡ-≤-neg-neg n m d n≤m

/ℕ-monoʳ-≤-nonNeg : ∀ n {d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
                    .{{_ : NonNegative n}} → d₁ ℕ.≤ d₂ → n /ℕ d₂ ≤ n /ℕ d₁
/ℕ-monoʳ-≤-nonNeg (+ n) {d₁} {d₂} d₁≤d₂ = +≤+ (ℕ./-monoʳ-≤ n d₁≤d₂)

/ℕ-monoʳ-≤-nonPos : ∀ n {d₁ d₂} .{{_ : ℕ.NonZero d₁}} .{{_ : ℕ.NonZero d₂}}
                    .{{_ : NonPositive n}} → d₁ ℕ.≤ d₂ → n /ℕ d₁ ≤ n /ℕ d₂
/ℕ-monoʳ-≤-nonPos (+ 0) {d₁} {d₂} d₁≤d₂ =
  ≤-trans (≤-reflexive (0/ℕd≡0 d₁)) (≤-reflexive (sym (0/ℕd≡0 d₂)))
/ℕ-monoʳ-≤-nonPos -[1+ n ] {d₁} {d₂} d₁≤d₂
  with ℕ.suc n ℕ.% d₁ in sn%d₁ | ℕ.suc n ℕ.% d₂ in sn%d₂
... | ℕ.zero | ℕ.zero  = neg-mono-≤ (+≤+ (ℕ./-monoʳ-≤ (ℕ.suc n) d₁≤d₂))
... | ℕ.zero | ℕ.suc _ = let sn%d₂>0 = n≡sk>0 sn%d₂ in begin
  -(+ (ℕ.suc n ℕ./ d₁)) ≡⟨ cong (-_ ∘′ +_) (ℕ.sn%d≡0⇒sn/d≡s[n/d] n d₁ sn%d₁) ⟩
  -[1+ n ℕ./ d₁ ]       ≤⟨ -≤- (ℕ./-monoʳ-≤ n d₁≤d₂) ⟩
  -[1+ n ℕ./ d₂ ]       ≡⟨ cong -[1+_] (ℕ.sn%d>0⇒sn/d≡n/d n d₂ sn%d₂>0) ⟨
  -[1+ ℕ.suc n ℕ./ d₂ ] ∎
... | ℕ.suc _ | ℕ.zero  = let sn%d₁>0 = n≡sk>0 sn%d₁ in begin
  -[1+ ℕ.suc n ℕ./ d₁ ]   ≡⟨ cong -[1+_] (ℕ.sn%d>0⇒sn/d≡n/d n d₁ sn%d₁>0) ⟩
  -[1+ n ℕ./ d₁ ]         ≤⟨ -≤- (ℕ./-monoʳ-≤ n d₁≤d₂) ⟩
  -(+ (ℕ.suc (n ℕ./ d₂))) ≡⟨ cong (-_ ∘′ +_) (ℕ.sn%d≡0⇒sn/d≡s[n/d] n d₂ sn%d₂)⟨
  -(+ (ℕ.suc n ℕ./ d₂))   ∎
... | ℕ.suc _ | ℕ.suc _ = -≤- (ℕ./-monoʳ-≤ (ℕ.suc n) d₁≤d₂)

/-monoˡ-≤-pos : ∀ d .{{_ : NonZero d}} .{{_ : Positive d}} →
                Monotonic₁ _≤_ _≤_ (_/ d)
/-monoˡ-≤-pos (+ d) {n} {m} n≤m = begin
  n / (+ d) ≡⟨ div-pos-is-/ℕ n d ⟩
  n /ℕ d    ≤⟨ /ℕ-monoˡ-≤ d n≤m ⟩
  m /ℕ d    ≡⟨ div-pos-is-/ℕ m d ⟨
  m / + d   ∎

/-monoˡ-≤-neg : ∀ d .{{_ : NonZero d}} .{{_ : Negative d}} →
                Monotonic₁ _≤_ _≥_ (_/ d)
/-monoˡ-≤-neg -[1+ d ] {n} {m} n≤m = begin
  m / -[1+ d ]     ≡⟨ div-neg-is-neg-/ℕ m (ℕ.suc d) ⟩
  - (m /ℕ ℕ.suc d) ≤⟨ neg-mono-≤ (/ℕ-monoˡ-≤ (ℕ.suc d) n≤m) ⟩
  - (n /ℕ ℕ.suc d) ≡⟨ div-neg-is-neg-/ℕ n (ℕ.suc d) ⟨
  n / - +[1+ d ]   ∎

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

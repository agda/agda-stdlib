------------------------------------------------------------------------
-- The Agda standard library
--
-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.GCD.Lemmas where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; sym)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

open ≡-Reasoning

private
  comm-factor : ∀ x k n → x * k + x * n ≡ x * (n + k)
  comm-factor x k n = begin
    x * k + x * n ≡⟨ +-comm (x * k) _ ⟩
    x * n + x * k ≡⟨ *-distribˡ-+ x n k ⟨
    x * (n + k)   ∎

  distrib-comm₂ : ∀ d x k n → d + x * (n + k) ≡ d + x * k + x * n
  distrib-comm₂ d x k n = begin
    d + x * (n + k)     ≡⟨ cong (d +_) (comm-factor x k n) ⟨
    d + (x * k + x * n) ≡⟨ +-assoc d _ _ ⟨
    d + x * k + x * n   ∎

-- Other properties
-- TODO: Can this proof be simplified? An automatic solver which can
-- handle ∸ would be nice...
lem₀ : ∀ i j m n → i * m ≡ j * m + n → (i ∸ j) * m ≡ n
lem₀ i j m n eq = begin
  (i ∸ j) * m            ≡⟨ *-distribʳ-∸ m i j ⟩
  (i * m) ∸ (j * m)      ≡⟨ cong (_∸ j * m) eq ⟩
  (j * m + n) ∸ (j * m)  ≡⟨ cong (_∸ j * m) (+-comm (j * m) n) ⟩
  (n + j * m) ∸ (j * m)  ≡⟨ m+n∸n≡m n (j * m) ⟩
  n                      ∎

lem₁ : ∀ i j → 2 + i ≤′ 2 + j + i
lem₁ i j = ≤⇒≤′ $ s≤s $ s≤s $ m≤n+m i j

private
  times2 : ∀ x → x + x ≡ 2 * x
  times2 x = cong (x +_) (sym (+-identityʳ x))

  times2′ : ∀ x y → x * y + x * y ≡ 2 * x * y
  times2′ x y = begin
    x * y + x * y ≡⟨ times2 (x * y) ⟩
    2 * (x * y)   ≡⟨ *-assoc 2 x y ⟨
    2 * x * y     ∎

lem₂ : ∀ d x {k n} →
       d + x * k ≡ x * n → d + x * (n + k) ≡ 2 * x * n
lem₂ d x {k} {n} eq = begin
  d + x * (n + k)    ≡⟨ distrib-comm₂ d x k n ⟩
  d + x * k + x * n  ≡⟨ cong (_+ x * n) eq ⟩
  x * n + x * n      ≡⟨ times2′ x n ⟩
  2 * x * n          ∎

private
  distrib₃ : ∀ a b c x → (a + b + c) * x ≡ a * x + b * x + c * x
  distrib₃ a b c x = begin
    (a + b + c) * x       ≡⟨ *-distribʳ-+ x (a + b) c ⟩
    (a + b) * x + c * x   ≡⟨ cong (_+ c * x) (*-distribʳ-+ x a b) ⟩
    a * x + b * x + c * x ∎

  lem₃₁ : ∀ a b c → a + (b + c) ≡ b + a + c
  lem₃₁ a b c = begin
    a + (b + c) ≡⟨ +-assoc a b c ⟨
    (a + b) + c ≡⟨ cong (_+ c) (+-comm a b) ⟩
    b + a + c   ∎

  +-assoc-comm : ∀ a b c d → a + (b + c + d) ≡ (a + c) + (b + d)
  +-assoc-comm a b c d = begin
    a + (b + c + d)   ≡⟨ cong (a +_) (cong (_+ d) (+-comm b c)) ⟩
    a + (c + b + d)   ≡⟨ cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d)) ≡⟨ +-assoc a c _ ⟨
    (a + c) + (b + d) ∎

  *-on-right : ∀ a b c {d} → b * c ≡ d → a * b * c ≡ a * d
  *-on-right a b c {d} eq = begin
    a * b * c   ≡⟨ *-assoc a b c ⟩
    a * (b * c) ≡⟨ cong (a *_) eq ⟩
    a * d       ∎

  *-on-left : ∀ a b c {d} → a * b ≡ d → a * (b * c) ≡ d * c
  *-on-left a b c {d} eq = begin
    a * (b * c) ≡⟨ *-assoc a b c ⟨
    a * b * c   ≡⟨ cong (_* c) eq ⟩
    d * c       ∎

  +-on-right : ∀ a b c {d} → b + c ≡ d → a + b + c ≡ a + d
  +-on-right a b c {d} eq = begin
    a + b + c   ≡⟨ +-assoc a b c ⟩
    a + (b + c) ≡⟨ cong (a +_) eq ⟩
    a + d       ∎

  +-on-left : ∀ a b c d → a + b ≡ d → a + (b + c) ≡ d + c
  +-on-left a b c d eq = begin
    a + (b + c) ≡⟨ +-assoc a b c ⟨
    a + b + c   ≡⟨ cong (_+ c) eq ⟩
    d + c       ∎

  +-focus-mid : ∀ a b c d → a + b + c + d ≡ a + (b + c) + d
  +-focus-mid a b c d = begin
    a + b + c + d     ≡⟨ cong (_+ d) (+-assoc a b c) ⟩
    a + (b + c) + d   ∎

  +-assoc-comm′ : ∀ a b c d → a + b + c + d ≡ a + (b + d) + c
  +-assoc-comm′ a b c d = begin
    a + b + c + d     ≡⟨ +-on-left a (b + c) d (a + b + c) (sym $ +-assoc a b c) ⟨
    a + (b + c + d)   ≡⟨ cong (a +_) (+-on-right b c d (+-comm c d)) ⟩
    a + (b + (d + c)) ≡⟨ cong (a +_) (+-assoc b d c) ⟨
    a + (b + d + c)   ≡⟨ +-assoc a _ c ⟨
    a + (b + d) + c   ∎

  lem₃₂ : ∀ a b c n → a * n + (b * n + a * n + c * n) ≡ (a + a + (b + c)) * n
  lem₃₂ a b c n = begin
    a * n + (b * n + a * n + c * n) ≡⟨ cong (a * n +_) (distrib₃ b a c n) ⟨
    a * n + (b + a + c) * n         ≡⟨ *-distribʳ-+ n a _ ⟨
    (a + (b + a + c)) * n           ≡⟨ cong (_* n) (+-assoc-comm a b a c) ⟩
    (a + a + (b + c)) * n           ∎

  mid-to-right : ∀ a b c → a + 2 * b + c ≡ (a + b + c) + b
  mid-to-right a b c = begin
    a + 2 * b + c   ≡⟨ cong (λ x → a + x + c) (times2 b) ⟨
    a + (b + b) + c ≡⟨ +-assoc-comm′ a b c b ⟨
    a + b + c + b   ∎

  mid-to-left : ∀ a b c → a + 2 * b + c ≡ b + (a + b + c)
  mid-to-left a b c = begin
    a + 2 * b + c   ≡⟨ cong (λ x → a + x + c) (times2 b) ⟨
    a + (b + b) + c ≡⟨ cong (_+ c) (+-on-left a b b _ (+-comm a b)) ⟩
    b + a + b + c   ≡⟨ +-on-left b (a + b) c (b + a + b) (sym $ +-assoc b a b) ⟨
    b + (a + b + c) ∎

lem₃ : ∀ d x {i k n} →
       d + (1 + x + i) * k ≡ x * n →
       d + (1 + x + i) * (n + k) ≡ (1 + 2 * x + i) * n
lem₃ d x {i} {k} {n} eq = begin
  d + y * (n + k)                     ≡⟨ distrib-comm₂ d y k n ⟩
  d + y * k + y * n                   ≡⟨ cong (_+ y * n) eq ⟩
  x * n + y * n                       ≡⟨ cong (x * n +_) (distrib₃ 1 x i n) ⟩
  x * n + (1 * n + x * n + i * n)     ≡⟨ lem₃₂ x 1 i n  ⟩
  (x + x + (1 + i)) * n               ≡⟨ cong (_* n) (cong (_+ (1 + i)) (times2 x)) ⟩
  (2 * x + (1 + i)) * n               ≡⟨ cong (_* n) (lem₃₁ (2 * x) 1 i) ⟩
  (1 + 2 * x + i) * n                 ∎
  where y = 1 + x + i

lem₄ : ∀ d y {k i} n →
       d + y * k ≡ (1 + y + i) * n →
       d + y * (n + k) ≡ (1 + 2 * y + i) * n
lem₄ d y {k} {i} n eq = begin
  d + y * (n + k)          ≡⟨ distrib-comm₂ d y k n ⟩
  d + y * k + y * n        ≡⟨ cong (_+ y * n) eq ⟩
  (1 + y + i) * n + y * n  ≡⟨ *-distribʳ-+ n (1 + y + i) y ⟨
  (1 + y + i + y) * n      ≡⟨ cong (_* n) (mid-to-right 1 y i) ⟨
  (1 + 2 * y + i) * n      ∎

lem₅ : ∀ d x {n k} →
       d + x * n ≡ x * k →
       d + 2 * x * n ≡ x * (n + k)
lem₅ d x {n} {k} eq = begin
  d + 2 * x * n       ≡⟨ cong (d +_) (times2′ x n) ⟨
  d + (x * n + x * n) ≡⟨ +-assoc d (x * n) _ ⟨
  d + x * n + x * n   ≡⟨ cong (_+ x * n) eq ⟩
  x * k + x * n       ≡⟨ comm-factor x k n ⟩
  x * (n + k)         ∎

lem₆ : ∀ d x {n i k} →
       d + x * n ≡ (1 + x + i) * k →
       d + (1 + 2 * x + i) * n ≡ (1 + x + i) * (n + k)
lem₆ d x {n} {i} {k} eq = begin
  d + (1 + 2 * x + i) * n  ≡⟨ cong (λ z → d + z * n) (mid-to-left 1 x i) ⟩
  d + (x + y) * n          ≡⟨ cong (d +_) (*-distribʳ-+ n x y) ⟩
  d + (x * n + y * n)      ≡⟨ +-on-left d _ _ _ eq ⟩
  y * k + y * n            ≡⟨ comm-factor y k n ⟩
  y * (n + k)              ∎
  where y = 1 + x + i

lem₇ : ∀ d y {i} n {k} →
       d + (1 + y + i) * n ≡ y * k →
       d + (1 + 2 * y + i) * n ≡ y * (n + k)
lem₇ d y {i} n {k} eq = begin
  d + (1 + 2 * y + i) * n       ≡⟨ cong (λ z → d + z * n) (mid-to-right 1 y i) ⟩
  d + (1 + y + i + y) * n       ≡⟨ cong (d +_) (*-distribʳ-+ n (1 + y + i) y) ⟩
  d + ((1 + y + i) * n + y * n) ≡⟨ +-on-left d _ _ _ eq ⟩
  y * k + y * n                 ≡⟨ comm-factor y k n ⟩
  y * (n + k)                   ∎

lem₈ : ∀ {i j k q} x y →
       1 + y * j ≡ x * i → j * k ≡ q * i →
       k ≡ (x * k ∸ y * q) * i
lem₈ {i} {j} {k} {q} x y eq eq′ =
  sym (lem₀ (x * k) (y * q) i k lemma)
  where
  lemma = begin
    x * k * i        ≡⟨ *-on-right x k i (*-comm k i) ⟩
    x * (i * k)      ≡⟨ *-on-left x i k (sym eq) ⟩
    (1 + y * j) * k  ≡⟨ +-comm k _ ⟩
    (y * j) * k + k  ≡⟨ cong (_+ k) (*-assoc y j k) ⟩
    y * (j * k) + k  ≡⟨ cong (λ n → y * n + k) eq′ ⟩
    y * (q * i) + k  ≡⟨ cong (_+ k) (*-assoc y q i)  ⟨
    y *  q * i  + k  ∎

lem₉ : ∀ {i j k q} x y →
       1 + x * i ≡ y * j → j * k ≡ q * i →
       k ≡ (y * q ∸ x * k) * i
lem₉ {i} {j} {k} {q} x y eq eq′ =
  sym (lem₀ (y * q) (x * k) i k lemma)
  where
  lem : ∀ a b c → a * b * c ≡ b * c * a
  lem a b c = begin
    a * b * c   ≡⟨ *-assoc a b c ⟩
    a * (b * c) ≡⟨ *-comm a _ ⟩
    b * c * a   ∎
  lemma = begin
    y * q * i        ≡⟨ lem y q i ⟩
    q * i * y        ≡⟨ cong (λ n → n * y) eq′ ⟨
    j * k * y        ≡⟨ lem y j k ⟨
    y * j * k        ≡⟨ cong (λ n → n * k) eq ⟨
    (1 + x * i) * k  ≡⟨ +-comm k _ ⟩
    x * i * k + k    ≡⟨ cong (_+ k) (*-on-right x i k (*-comm i k)) ⟩
    x * (k * i) + k  ≡⟨ cong (_+ k) (*-assoc x k i) ⟨
    x * k * i + k    ∎

lem₁₀ : ∀ {a′} b c {d} e f → let a = suc a′ in
        a + b * (c * d * a) ≡ e * (f * d * a) →
        d ≡ 1
lem₁₀ {a′} b c {d} e f eq =
  m*n≡1⇒n≡1 (e * f ∸ b * c) d
    (lem₀ (e * f) (b * c) d 1
       (*-cancelʳ-≡ (e * f * d) (b * c * d + 1) _ (begin
          e * f * d * a           ≡⟨ *-assoc₄₃ e f d a ⟩
          e * (f * d * a)         ≡⟨ eq ⟨
          a + b * (c * d * a)     ≡⟨ cong (a +_) (*-assoc₄₃ b c d a) ⟨
          a + b * c * d * a       ≡⟨ +-comm a _ ⟩
          b * c * d * a + a       ≡⟨ cong (b * c * d * a +_) (+-identityʳ a) ⟨
          b * c * d * a + (a + 0) ≡⟨ *-distribʳ-+ a (b * c * d) 1 ⟨
          (b * c * d + 1) * a     ∎)))
  where a = suc a′
        *-assoc₄₃ : ∀ w x y z → w * x * y * z ≡ w * (x * y * z)
        *-assoc₄₃ w x y z = begin
          w * x * y * z   ≡⟨ cong (_* z) (*-assoc w x y) ⟩
          w * (x * y) * z ≡⟨ *-assoc w _ z ⟩
          w * (x * y * z) ∎

lem₁₁ : ∀ {i j m n k d} x y →
       1 + y * j ≡ x * i → i * k ≡ m * d → j * k ≡ n * d →
       k ≡ (x * m ∸ y * n) * d
lem₁₁ {i} {j} {m} {n} {k} {d} x y eq eq₁ eq₂ =
  sym (lem₀ (x * m) (y * n) d k (begin
    x * m * d        ≡⟨ *-on-right x m d (sym eq₁) ⟩
    x * (i * k)      ≡⟨ *-on-left x i k (sym eq) ⟩
    (1 + y * j) * k  ≡⟨ +-comm k _ ⟩
    y * j * k + k    ≡⟨ cong (_+ k) (*-assoc y j k) ⟩
    y * (j * k) + k  ≡⟨ cong (λ p → y * p + k) eq₂ ⟩
    y * (n * d) + k  ≡⟨ cong (_+ k) (*-assoc y n d) ⟨
    y * n * d + k    ∎))

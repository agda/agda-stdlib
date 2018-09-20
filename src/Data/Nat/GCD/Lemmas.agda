------------------------------------------------------------------------
-- The Agda standard library
--
-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
------------------------------------------------------------------------

module Data.Nat.GCD.Lemmas where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Function
open import Relation.Binary.PropositionalEquality

open +-*-Solver
open ≡-Reasoning

private
  distrib-comm : ∀ x k n → x * k + x * n ≡ x * (n + k)
  distrib-comm =
    solve 3 (λ x k n → x :* k :+ x :* n  :=  x :* (n :+ k)) refl

  distrib-comm₂ : ∀ d x k n → d + x * (n + k) ≡ d + x * k + x * n
  distrib-comm₂ =
    solve 4 (λ d x k n → d :+ x :* (n :+ k) :=  d :+ x :* k :+ x :* n) refl

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
lem₁ i j = ≤⇒≤′ $ s≤s $ s≤s $ n≤m+n j i

lem₂ : ∀ d x {k n} →
       d + x * k ≡ x * n → d + x * (n + k) ≡ 2 * x * n
lem₂ d x {k} {n} eq = begin
  d + x * (n + k)    ≡⟨ distrib-comm₂ d x k n ⟩
  d + x * k + x * n  ≡⟨ cong₂ _+_ eq refl ⟩
  x * n + x * n      ≡⟨ solve 3 (λ x n k → x :* n :+ x :* n
                                       :=  con 2 :* x :* n)
                                 refl x n k ⟩
  2 * x * n          ∎

lem₃ : ∀ d x {i k n} →
       d + (1 + x + i) * k ≡ x * n →
       d + (1 + x + i) * (n + k) ≡ (1 + 2 * x + i) * n
lem₃ d x {i} {k} {n} eq = begin
  d + y * (n + k)      ≡⟨ distrib-comm₂ d y k n ⟩
  d + y * k + y * n    ≡⟨ cong₂ _+_ eq refl ⟩
  x * n + y * n        ≡⟨ solve 3 (λ x n i → x :* n :+ (con 1 :+ x :+ i) :* n
                                         :=  (con 1 :+ con 2 :* x :+ i) :* n)
                                  refl x n i ⟩
  (1 + 2 * x + i) * n  ∎
  where y = 1 + x + i

lem₄ : ∀ d y {k i} n →
       d + y * k ≡ (1 + y + i) * n →
       d + y * (n + k) ≡ (1 + 2 * y + i) * n
lem₄ d y {k} {i} n eq = begin
  d + y * (n + k)          ≡⟨ distrib-comm₂ d y k n ⟩
  d + y * k + y * n        ≡⟨ cong₂ _+_ eq refl ⟩
  (1 + y + i) * n + y * n  ≡⟨ solve 3 (λ y i n → (con 1 :+ y :+ i) :* n :+ y :* n
                                             :=  (con 1 :+ con 2 :* y :+ i) :* n)
                                      refl y i n ⟩
  (1 + 2 * y + i) * n      ∎

lem₅ : ∀ d x {n k} →
       d + x * n ≡ x * k →
       d + 2 * x * n ≡ x * (n + k)
lem₅ d x {n} {k} eq = begin
  d + 2 * x * n      ≡⟨ solve 3 (λ d x n → d :+ con 2 :* x :* n
                                       :=  d :+ x :* n :+ x :* n)
                                refl d x n ⟩
  d + x * n + x * n  ≡⟨ cong₂ _+_ eq refl ⟩
  x * k + x * n      ≡⟨ distrib-comm x k n ⟩
  x * (n + k)        ∎

lem₆ : ∀ d x {n i k} →
       d + x * n ≡ (1 + x + i) * k →
       d + (1 + 2 * x + i) * n ≡ (1 + x + i) * (n + k)
lem₆ d x {n} {i} {k} eq = begin
  d + (1 + 2 * x + i) * n  ≡⟨ solve 4 (λ d x i n → d :+ (con 1 :+ con 2 :* x :+ i) :* n
                                               :=  d :+ x :* n :+ (con 1 :+ x :+ i) :* n)
                                      refl d x i n ⟩
  d + x * n + y * n        ≡⟨ cong₂ _+_ eq refl ⟩
  y * k + y * n            ≡⟨ distrib-comm y k n ⟩
  y * (n + k)              ∎
  where y = 1 + x + i

lem₇ : ∀ d y {i} n {k} →
       d + (1 + y + i) * n ≡ y * k →
       d + (1 + 2 * y + i) * n ≡ y * (n + k)
lem₇ d y {i} n {k} eq = begin
  d + (1 + 2 * y + i) * n      ≡⟨ solve 4 (λ d y i n → d :+ (con 1 :+ con 2 :* y :+ i) :* n
                                                   :=  d :+ (con 1 :+ y :+ i) :* n :+ y :* n)
                                          refl d y i n ⟩
  d + (1 + y + i) * n + y * n  ≡⟨ cong₂ _+_ eq refl ⟩
  y * k + y * n                ≡⟨ distrib-comm y k n ⟩
  y * (n + k)                  ∎

lem₈ : ∀ {i j k q} x y →
       1 + y * j ≡ x * i → j * k ≡ q * i →
       k ≡ (x * k ∸ y * q) * i
lem₈ {i} {j} {k} {q} x y eq eq′ =
  sym (lem₀ (x * k) (y * q) i k lemma)
  where
  lemma = begin
    x * k * i        ≡⟨ solve 3 (λ x k i → x :* k :* i
                                       :=  x :* i :* k)
                                refl x k i ⟩
    x * i * k        ≡⟨ cong (_* k) (sym eq) ⟩
    (1 + y * j) * k  ≡⟨ solve 3 (λ y j k → (con 1 :+ y :* j) :* k
                                       :=  y :* (j :* k) :+ k)
                                refl y j k ⟩
    y * (j * k) + k  ≡⟨ cong (λ n → y * n + k) eq′ ⟩
    y * (q * i) + k  ≡⟨ solve 4 (λ y q i k → y :* (q :* i) :+ k
                                         :=  y :*  q :* i  :+ k)
                                refl y q i k ⟩
    y *  q * i  + k  ∎

lem₉ : ∀ {i j k q} x y →
       1 + x * i ≡ y * j → j * k ≡ q * i →
       k ≡ (y * q ∸ x * k) * i
lem₉ {i} {j} {k} {q} x y eq eq′ =
  sym (lem₀ (y * q) (x * k) i k lemma)
  where
  lem   = solve 3 (λ a b c → a :* b :* c  :=  b :* c :* a) refl
  lemma = begin
    y * q * i        ≡⟨ lem y q i ⟩
    q * i * y        ≡⟨ cong (λ n → n * y) (sym eq′) ⟩
    j * k * y        ≡⟨ sym (lem y j k) ⟩
    y * j * k        ≡⟨ cong (λ n → n * k) (sym eq) ⟩
    (1 + x * i) * k  ≡⟨ solve 3 (λ x i k → (con 1 :+ x :* i) :* k
                                       :=  x :* k :* i :+ k)
                                refl x i k ⟩
    x * k * i + k    ∎

lem₁₀ : ∀ {a′} b c {d} e f → let a = suc a′ in
        a + b * (c * d * a) ≡ e * (f * d * a) →
        d ≡ 1
lem₁₀ {a′} b c {d} e f eq =
  i*j≡1⇒j≡1 (e * f ∸ b * c) d
    (lem₀ (e * f) (b * c) d 1
       (*-cancelʳ-≡ (e * f * d) (b * c * d + 1) (begin
          e * f * d * a        ≡⟨ solve 4 (λ e f d a → e :* f :* d :* a
                                                   :=  e :* (f :* d :* a))
                                          refl e f d a ⟩
          e * (f * d * a)      ≡⟨ sym eq ⟩
          a + b * (c * d * a)  ≡⟨ solve 4 (λ a b c d → a :+ b :* (c :* d :* a)
                                                   :=  (b :* c :* d :+ con 1) :* a)
                                          refl a b c d ⟩
          (b * c * d + 1) * a  ∎)))
  where a = suc a′

lem₁₁ : ∀ {i j m n k d} x y →
       1 + y * j ≡ x * i → i * k ≡ m * d → j * k ≡ n * d →
       k ≡ (x * m ∸ y * n) * d
lem₁₁ {i} {j} {m} {n} {k} {d} x y eq eq₁ eq₂ =
  sym (lem₀ (x * m) (y * n) d k (begin
    x * m * d        ≡⟨ *-assoc x m d ⟩
    x * (m * d)      ≡⟨ cong (x *_) (sym eq₁) ⟩
    x * (i * k)      ≡⟨ sym (*-assoc x i k) ⟩
    x * i * k        ≡⟨ cong₂ _*_ (sym eq) refl ⟩
    (1 + y * j) * k  ≡⟨ solve 3 (λ y j k → (con 1 :+ y :* j) :* k
                                       :=  y :* (j :* k) :+ k)
                                refl y j k ⟩
    y * (j * k) + k  ≡⟨ cong (λ p → y * p + k) eq₂ ⟩
    y * (n * d) + k  ≡⟨ cong₂ _+_ (sym $ *-assoc y n d) refl ⟩
    y * n * d + k    ∎))

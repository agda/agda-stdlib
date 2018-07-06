------------------------------------------------------------------------
-- The Agda standard library
--
-- Core lemmas for division and modulus operations
------------------------------------------------------------------------

module Data.Nat.DivMod.Core where

open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-------------------------------------------------------------------------
-- mod lemmas

modₕ-skipTo0 : ∀ acc n a b → modₕ acc n (b + a) a ≡ modₕ (a + acc) n b 0
modₕ-skipTo0 acc n zero    b = cong (λ v → modₕ acc n v 0) (+-identityʳ b)
modₕ-skipTo0 acc n (suc a) b = begin
  modₕ acc n (b + suc a) (suc a) ≡⟨ cong (λ v → modₕ acc n v (suc a)) (+-suc b a) ⟩
  modₕ acc n (suc b + a) (suc a) ≡⟨⟩
  modₕ (suc acc) n (b + a) a     ≡⟨ modₕ-skipTo0 (suc acc) n a b ⟩
  modₕ (a + suc acc) n b 0       ≡⟨ cong (λ v → modₕ v n b 0) (+-suc a acc) ⟩
  modₕ (suc a + acc) n b 0       ∎

modₕ-skipToEnd : ∀ acc n a b → modₕ acc n a (a + b) ≡ acc + a
modₕ-skipToEnd acc n zero    b = sym (+-identityʳ acc)
modₕ-skipToEnd acc n (suc a) b = begin
  modₕ (suc acc) n a (a + b) ≡⟨ modₕ-skipToEnd (suc acc) n a b ⟩
  suc acc + a                ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                ∎

a[modₕ]1≡0 : ∀ a → modₕ 0 0 a 0 ≡ 0
a[modₕ]1≡0 zero    = refl
a[modₕ]1≡0 (suc a) = a[modₕ]1≡0 a

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ≡ 0
n[modₕ]n≡0 acc v = modₕ-skipTo0 acc (acc + v) v 1

a[modₕ]n<n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n<n acc zero    n       = m≤m+n acc n
a[modₕ]n<n acc (suc d) zero    = a[modₕ]n<n zero d (acc + 0)
a[modₕ]n<n acc (suc d) (suc n)
           rewrite +-suc acc n = a[modₕ]n<n (suc acc) d n

modₕ-idem : ∀ acc a n → modₕ 0 (acc + n) (modₕ acc (acc + n) a n) (acc + n) ≡ modₕ acc (acc + n) a n
modₕ-idem acc zero    n       = modₕ-skipToEnd 0 (acc + n) acc n
modₕ-idem acc (suc a) zero    rewrite +-identityʳ acc = modₕ-idem 0 a acc
modₕ-idem acc (suc a) (suc n) rewrite +-suc acc n = modₕ-idem (suc acc) a n

a+n[modₕ]n≡a[modₕ]n : ∀ acc a n → modₕ acc (acc + n) (acc + a + suc n) n ≡ modₕ acc (acc + n) a n
a+n[modₕ]n≡a[modₕ]n acc zero n rewrite +-identityʳ acc = begin
  modₕ acc (acc + n) (acc + suc n) n   ≡⟨ cong (λ v → modₕ acc (acc + n) v n) (+-suc acc n) ⟩
  modₕ acc (acc + n) (suc acc + n) n   ≡⟨ modₕ-skipTo0 acc (acc + n) n (suc acc) ⟩
  modₕ (acc + n) (acc + n) (suc acc) 0 ≡⟨⟩
  modₕ 0 (acc + n) acc (acc + n)       ≡⟨ modₕ-skipToEnd 0 (acc + n) acc n ⟩
  acc                                  ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) zero rewrite +-identityʳ acc = begin
  modₕ acc acc (acc + suc a + 1)   0   ≡⟨ cong (λ v → modₕ acc acc v 0) (+-comm (acc + suc a) 1) ⟩
  modₕ acc acc (1 + (acc + suc a)) 0   ≡⟨⟩
  modₕ 0   acc (acc + suc a)       acc ≡⟨ cong (λ v → modₕ 0 acc v acc) (+-comm acc (suc a)) ⟩
  modₕ 0   acc (suc a + acc)       acc ≡⟨ cong (λ v → modₕ 0 acc v acc) (sym (+-suc a acc)) ⟩
  modₕ 0   acc (a + suc acc)       acc ≡⟨ a+n[modₕ]n≡a[modₕ]n 0 a acc ⟩
  modₕ 0   acc a                   acc ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) (suc n) rewrite +-suc acc n = begin
  mod₁ (acc + suc a + (2 + n)) (suc n) ≡⟨ cong (λ v → mod₁ (v + suc (suc n)) (suc n)) (+-suc acc a) ⟩
  mod₁ (suc acc + a + (2 + n)) (suc n) ≡⟨⟩
  mod₂ (acc + a + (2 + n))     n       ≡⟨ cong (λ v → mod₂ v n) (sym (+-assoc (acc + a) 1 (suc n))) ⟩
  mod₂ (acc + a + 1 + suc n)   n       ≡⟨ cong (λ v → mod₂ (v + suc n) n) (+-comm (acc + a) 1) ⟩
  mod₂ (suc acc + a + suc n)   n       ≡⟨ a+n[modₕ]n≡a[modₕ]n (suc acc) a n ⟩
  mod₂ a                       n       ∎
  where
  mod₁ = modₕ acc       (suc acc + n)
  mod₂ = modₕ (suc acc) (suc acc + n)

-------------------------------------------------------------------------
-- division lemmas

-- The quotient and remainder are related to the dividend and
-- divisor in the right way.

division-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ * suc (accᵐ + n) + d ≡
    modₕ accᵐ (accᵐ + n) d n + divₕ accᵈ (accᵐ + n) d n * suc (accᵐ + n)
division-lemma accᵐ accᵈ zero    n    = +-identityʳ _
division-lemma accᵐ accᵈ (suc d) zero rewrite +-identityʳ accᵐ = begin
  accᵐ + accᵈ * suc accᵐ + suc d          ≡⟨ +-suc _ d ⟩
  suc accᵈ * suc accᵐ + d                 ≡⟨ division-lemma zero (suc accᵈ) d accᵐ ⟩
  modₕ 0          accᵐ d accᵐ +
  divₕ (suc accᵈ) accᵐ d accᵐ * suc accᵐ  ≡⟨⟩
  modₕ accᵐ accᵐ (suc d) 0 +
  divₕ accᵈ accᵐ (suc d) 0 * suc accᵐ     ∎
division-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin
  accᵐ + accᵈ * m + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * m + d)           ≡⟨ division-lemma (suc accᵐ) accᵈ d n ⟩
  modₕ _ _ d n + divₕ accᵈ _ d n * m  ∎
  where
  m = 2 + accᵐ + n

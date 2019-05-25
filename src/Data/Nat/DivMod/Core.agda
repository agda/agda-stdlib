------------------------------------------------------------------------
-- The Agda standard library
--
-- Core lemmas for division and modulus operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.DivMod.Core where

open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open ≤-Reasoning

-------------------------------------------------------------------------
-- mod helper lemmas

private

  mod-cong₃ : ∀ {c n a₁ a₂ b} → a₁ ≡ a₂ → modₕ c n a₁ b ≡ modₕ c n a₂ b
  mod-cong₃ refl = refl

  modₕ-skipTo0 : ∀ acc n a b → modₕ acc n (b + a) a ≡ modₕ (a + acc) n b 0
  modₕ-skipTo0 acc n zero    b = cong (λ v → modₕ acc n v 0) (+-identityʳ b)
  modₕ-skipTo0 acc n (suc a) b = begin-equality
    modₕ acc n (b + suc a) (suc a) ≡⟨ mod-cong₃ (+-suc b a) ⟩
    modₕ acc n (suc b + a) (suc a) ≡⟨⟩
    modₕ (suc acc) n (b + a) a     ≡⟨ modₕ-skipTo0 (suc acc) n a b ⟩
    modₕ (a + suc acc) n b 0       ≡⟨ cong (λ v → modₕ v n b 0) (+-suc a acc) ⟩
    modₕ (suc a + acc) n b 0       ∎

  modₕ-skipToEnd : ∀ acc n a b → modₕ acc n a (a + b) ≡ acc + a
  modₕ-skipToEnd acc n zero    b = sym (+-identityʳ acc)
  modₕ-skipToEnd acc n (suc a) b = begin-equality
    modₕ (suc acc) n a (a + b) ≡⟨ modₕ-skipToEnd (suc acc) n a b ⟩
    suc acc + a                ≡⟨ sym (+-suc acc a) ⟩
    acc + suc a                ∎

-------------------------------------------------------------------------
-- mod real lemmas

a[modₕ]1≡0 : ∀ a → modₕ 0 0 a 0 ≡ 0
a[modₕ]1≡0 zero    = refl
a[modₕ]1≡0 (suc a) = a[modₕ]1≡0 a

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ≡ 0
n[modₕ]n≡0 acc v = modₕ-skipTo0 acc (acc + v) v 1

a[modₕ]n<n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n<n acc zero    n       = m≤m+n acc n
a[modₕ]n<n acc (suc d) zero    = a[modₕ]n<n zero d (acc + 0)
a[modₕ]n<n acc (suc d) (suc n) rewrite +-suc acc n = a[modₕ]n<n (suc acc) d n

a[modₕ]n≤a : ∀ acc a n → modₕ acc (acc + n) a n ≤ acc + a
a[modₕ]n≤a acc zero    n       = ≤-reflexive (sym (+-identityʳ acc))
a[modₕ]n≤a acc (suc a) (suc n) = begin
  modₕ acc (acc + suc n) (suc a) (suc n) ≡⟨ cong (λ v → modₕ acc v (suc a) (suc n)) (+-suc acc n) ⟩
  modₕ acc (suc acc + n) (suc a) (suc n) ≤⟨ a[modₕ]n≤a (suc acc) a n ⟩
  suc acc + a                            ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                            ∎
a[modₕ]n≤a acc (suc a) zero    = begin
  modₕ acc (acc + 0) (suc a) 0 ≡⟨ cong (λ v → modₕ acc v (suc a) 0) (+-identityʳ acc) ⟩
  modₕ acc acc (suc a) 0       ≤⟨ a[modₕ]n≤a 0 a acc ⟩
  a                            ≤⟨ n≤1+n a ⟩
  suc a                        ≤⟨ m≤n+m (suc a) acc ⟩
  acc + suc a                  ∎

modₕ-idem : ∀ acc a n → modₕ 0 (acc + n) (modₕ acc (acc + n) a n) (acc + n) ≡ modₕ acc (acc + n) a n
modₕ-idem acc zero    n       = modₕ-skipToEnd 0 (acc + n) acc n
modₕ-idem acc (suc a) zero    rewrite +-identityʳ acc = modₕ-idem 0 a acc
modₕ-idem acc (suc a) (suc n) rewrite +-suc acc n = modₕ-idem (suc acc) a n

a+n[modₕ]n≡a[modₕ]n : ∀ acc a n → modₕ acc (acc + n) (acc + a + suc n) n ≡ modₕ acc (acc + n) a n
a+n[modₕ]n≡a[modₕ]n acc zero n rewrite +-identityʳ acc = begin-equality
  modₕ acc (acc + n) (acc + suc n) n   ≡⟨ mod-cong₃ (+-suc acc n) ⟩
  modₕ acc (acc + n) (suc acc + n) n   ≡⟨ modₕ-skipTo0 acc (acc + n) n (suc acc) ⟩
  modₕ (acc + n) (acc + n) (suc acc) 0 ≡⟨⟩
  modₕ 0 (acc + n) acc (acc + n)       ≡⟨ modₕ-skipToEnd 0 (acc + n) acc n ⟩
  acc                                  ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) zero rewrite +-identityʳ acc = begin-equality
  modₕ acc acc (acc + suc a + 1)   0   ≡⟨ mod-cong₃ (+-comm (acc + suc a) 1) ⟩
  modₕ acc acc (1 + (acc + suc a)) 0   ≡⟨⟩
  modₕ 0   acc (acc + suc a)       acc ≡⟨ mod-cong₃ (+-comm acc (suc a)) ⟩
  modₕ 0   acc (suc a + acc)       acc ≡⟨ mod-cong₃ (sym (+-suc a acc)) ⟩
  modₕ 0   acc (a + suc acc)       acc ≡⟨ a+n[modₕ]n≡a[modₕ]n 0 a acc ⟩
  modₕ 0   acc a                   acc ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) (suc n) rewrite +-suc acc n = begin-equality
  mod₁ (acc + suc a + (2 + n)) (suc n) ≡⟨ cong (λ v → mod₁ (v + suc (suc n)) (suc n)) (+-suc acc a) ⟩
  mod₁ (suc acc + a + (2 + n)) (suc n) ≡⟨⟩
  mod₂ (acc + a + (2 + n))     n       ≡⟨ mod-cong₃ (sym (+-assoc (acc + a) 1 (suc n))) ⟩
  mod₂ (acc + a + 1 + suc n)   n       ≡⟨ mod-cong₃ (cong (_+ suc n) (+-comm (acc + a) 1)) ⟩
  mod₂ (suc acc + a + suc n)   n       ≡⟨ a+n[modₕ]n≡a[modₕ]n (suc acc) a n ⟩
  mod₂ a                       n       ∎
  where
  mod₁ = modₕ acc       (suc acc + n)
  mod₂ = modₕ (suc acc) (suc acc + n)

-------------------------------------------------------------------------
-- division helper lemmas

private

  div-cong₃ : ∀ {c n a₁ a₂ b} → a₁ ≡ a₂ → divₕ c n a₁ b ≡ divₕ c n a₂ b
  div-cong₃ refl = refl

  divₕ-restart : ∀ k m n j → j < n → divₕ k m n j ≡ divₕ (suc k) m (n ∸ suc j) m
  divₕ-restart k m (suc n) zero    j<n       = refl
  divₕ-restart k m (suc n) (suc j) (s≤s j<n) = divₕ-restart k m n j j<n

  divₕ-finish : ∀ k m n j → j ≥ n → divₕ k m n j ≡ k
  divₕ-finish k m zero    j       j≥n       = refl
  divₕ-finish k m (suc n) (suc j) (s≤s j≥n) = divₕ-finish k m n j j≥n

  divₕ-extractAcc : ∀ k m n j → divₕ k m n j ≡ k + divₕ 0 m n j
  divₕ-extractAcc k m zero j          = sym (+-identityʳ k)
  divₕ-extractAcc k m (suc n) (suc j) = divₕ-extractAcc k m n j
  divₕ-extractAcc k m (suc n) zero = begin-equality
    divₕ (suc k)    m n m  ≡⟨ divₕ-extractAcc (suc k) m n m ⟩
    suc k +  divₕ 0 m n m  ≡⟨ sym (+-suc k _) ⟩
    k + suc (divₕ 0 m n m) ≡⟨ cong (k +_) (sym (divₕ-extractAcc 1 m n m)) ⟩
    k +      divₕ 1 m n m  ∎

-------------------------------------------------------------------------
-- division lemmas

-- The quotient and remainder are related to the dividend and
-- divisor in the right way.

division-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ * suc (accᵐ + n) + d ≡
    modₕ accᵐ (accᵐ + n) d n + divₕ accᵈ (accᵐ + n) d n * suc (accᵐ + n)
division-lemma accᵐ accᵈ zero    n    = +-identityʳ _
division-lemma accᵐ accᵈ (suc d) zero rewrite +-identityʳ accᵐ = begin-equality
  accᵐ + accᵈ * suc accᵐ + suc d          ≡⟨ +-suc _ d ⟩
  suc accᵈ * suc accᵐ + d                 ≡⟨ division-lemma zero (suc accᵈ) d accᵐ ⟩
  modₕ 0          accᵐ d accᵐ +
  divₕ (suc accᵈ) accᵐ d accᵐ * suc accᵐ  ≡⟨⟩
  modₕ accᵐ accᵐ (suc d) 0 +
  divₕ accᵈ accᵐ (suc d) 0 * suc accᵐ     ∎
division-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin-equality
  accᵐ + accᵈ * m + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * m + d)           ≡⟨ division-lemma (suc accᵐ) accᵈ d n ⟩
  modₕ _ _ d n + divₕ accᵈ _ d n * m  ∎
  where
  m = 2 + accᵐ + n

n[divₕ]n≡1 : ∀ n m → divₕ 0 n (suc m) m ≡ 1
n[divₕ]n≡1 n zero    = refl
n[divₕ]n≡1 n (suc m) = n[divₕ]n≡1 n m

a[divₕ]1≡a : ∀ acc a → divₕ acc 0 a 0 ≡ acc + a
a[divₕ]1≡a acc zero    = sym (+-identityʳ acc)
a[divₕ]1≡a acc (suc a) = trans (a[divₕ]1≡a (suc acc) a) (sym (+-suc acc a))

a*n[divₕ]n≡a : ∀ acc a n → divₕ acc n (a * suc n) n ≡ acc + a
a*n[divₕ]n≡a acc zero    n = sym (+-identityʳ acc)
a*n[divₕ]n≡a acc (suc a) n = begin-equality
  divₕ acc       n (suc a * suc n)             n ≡⟨ divₕ-restart acc n (suc a * suc n) n (m≤m+n (suc n) _) ⟩
  divₕ (suc acc) n (suc a * suc n ∸ suc n)     n ≡⟨⟩
  divₕ (suc acc) n (suc n + a * suc n ∸ suc n) n ≡⟨ div-cong₃ (m+n∸m≡n (suc n) (a * suc n)) ⟩
  divₕ (suc acc) n (a * suc n)                 n ≡⟨ a*n[divₕ]n≡a (suc acc) a n ⟩
  suc acc + a                                    ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                                    ∎

+-distrib-divₕ-orig : ∀ d m n → modₕ 0 d m d + modₕ 0 d n d < suc d →
                      divₕ 0 d (m + n) d ≡ divₕ 0 d m d + divₕ 0 d n d
+-distrib-divₕ-orig d m n leq = {!!}



-- (n mod (1+d) - j) / (1 + d) ≡ (n mod (1+d) - k) / (1 + d)

-- n = l(1+d) + n mod (1+d)

divₕ-eq : ∀ d n j k → modₕ 0 d n d ∸ j + modₕ 0 d n d ∸ k < suc d → divₕ 0 d n j ≡ divₕ 0 d n k
divₕ-eq d n j = {!!}

+-distrib-divₕ : ∀ acc d m n j k → modₕ k d m j + modₕ 0 d n d < suc d →
                 divₕ acc d (m + n) j ≡ divₕ acc d m j + divₕ 0 d n d
+-distrib-divₕ acc d (suc m) n (suc j) k leq = +-distrib-divₕ acc d m n j (suc k) leq
+-distrib-divₕ acc d (suc m) n zero    k leq = +-distrib-divₕ (suc acc) d m n d 0 leq
+-distrib-divₕ acc d zero    n j       k leq = begin-equality
  divₕ acc d n j     ≡⟨ divₕ-extractAcc acc d n j ⟩
  acc + divₕ 0 d n j ≡⟨ cong (acc +_) {!!} ⟩
  acc + divₕ 0 d n d ∎

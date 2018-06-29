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

a[modₕ]1≡0 : ∀ a → modₕ 0 0 a 0 ≡ 0
a[modₕ]1≡0 zero    = refl
a[modₕ]1≡0 (suc a) = a[modₕ]1≡0 a

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ≡ 0
n[modₕ]n≡0 acc       zero    = refl
n[modₕ]n≡0 zero      (suc v) = n[modₕ]n≡0 1 v
n[modₕ]n≡0 (suc acc) (suc v)
         rewrite +-suc acc v = n[modₕ]n≡0 (2 + acc) v

mod-lemma : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
mod-lemma acc zero    n       = m≤m+n acc n
mod-lemma acc (suc d) zero    = mod-lemma zero d (acc + 0)
mod-lemma acc (suc d) (suc n)
          rewrite +-suc acc n = mod-lemma (suc acc) d n

lemma2 : ∀ acc a n → modₕ acc (acc + a + n) a (a + n) ≡ acc + a
lemma2 acc zero    n = sym (+-identityʳ acc)
lemma2 acc (suc a) n rewrite +-suc acc a = lemma2 (suc acc) a n

modₕ-absorb : ∀ acc a n → modₕ 0 (acc + n) (modₕ acc (acc + n) a n) (acc + n) ≡ modₕ acc (acc + n) a n
modₕ-absorb acc zero    n       = lemma2 0 acc n
modₕ-absorb acc (suc a) zero    rewrite +-identityʳ acc = modₕ-absorb 0 a acc
modₕ-absorb acc (suc a) (suc n) rewrite +-suc acc n = modₕ-absorb (suc acc) a n

modₕ-distribˡ-+2 : ∀ a b n → modₕ 0 n (a + b) n ≡ modₕ 0 n (modₕ 0 n a n + modₕ 0 n b n) n
modₕ-distribˡ-+2 (suc a) (suc b) (suc n) = {!!}
modₕ-distribˡ-+2 (suc a) (suc b) (suc (suc n)) = {!!}
modₕ-distribˡ-+2 (suc a) (suc b) (suc (suc (suc n))) = {!!}
modₕ-distribˡ-+2 (suc (suc a)) (suc b) (suc n) = {!!}
modₕ-distribˡ-+2 (suc (suc (suc a))) (suc b) (suc n) = {!!}


lemma4 : ∀ acc → modₕ acc acc acc 0 ≡ modₕ 0 acc (acc + acc) acc
lemma4 zero = refl
lemma4 (suc zero) = refl
lemma4 (suc (suc zero)) = refl
lemma4 (suc (suc (suc acc))) = {!!}

lemma5 : ∀ acc a → modₕ acc (acc + suc a) a (suc a) ≡ modₕ (suc acc) (acc + suc a) (a + acc + a) a
lemma5 5 9 = {!!}


lemma3 : ∀ acc b n → modₕ acc (acc + n) (acc + b) n ≡
                     modₕ 0 (acc + n) (acc + modₕ acc (acc + n) b n) (acc + n)
lemma3 zero      zero    zero = refl
lemma3 (suc acc) zero    zero rewrite +-identityʳ acc = {!!}
lemma3 acc       zero    (suc b) = {!!}
lemma3 acc       (suc a) (suc b) = {!!}
lemma3 6         8       13      = {!!}

modₕ-distribˡ-+ : ∀ acc a b n → modₕ acc (acc + n) (a + acc + b) n ≡
                                modₕ 0 (acc + n) (modₕ acc (acc + n) a n + modₕ acc (acc + n) b n) (acc + n)
modₕ-distribˡ-+ acc a zero n rewrite +-identityʳ (a + acc) = begin
  _ ≡⟨ cong (λ v → modₕ acc (acc + n) v n) (+-comm a acc) ⟩
  _ ≡⟨ lemma3 acc a n ⟩
  _ ≡⟨ cong (λ v → modₕ 0 (acc + n) v (acc + n)) (+-comm acc _) ⟩
  _                                ∎
modₕ-distribˡ-+ acc zero b n = lemma3 acc b n
modₕ-distribˡ-+ acc (suc a) (suc b) zero = {!!}
modₕ-distribˡ-+ acc (suc a) (suc b) (suc n) rewrite +-suc acc n = begin
  modₕ (suc acc) (suc (acc + n)) (a + acc + suc b) n ≡⟨ cong (λ v → modₕ (suc acc) (suc acc + n) v n) {x = a + acc + suc b} {y = a + suc acc + b} {!!} ⟩
  modₕ (suc acc) (suc (acc + n)) (a + suc acc + b) n ≡⟨ modₕ-distribˡ-+ (suc acc) a b n ⟩
  _                               ∎

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
  divₕ accᵈ accᵐ (suc d) 0 * suc accᵐ      ∎
division-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin
  accᵐ + accᵈ * (2 + accᵐ + n) + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * (2 + accᵐ + n) + d)           ≡⟨ division-lemma (suc accᵐ) accᵈ d n ⟩
  modₕ (suc accᵐ) (suc (accᵐ + n)) d n +
  divₕ accᵈ (suc (accᵐ + n)) d n * (2 + accᵐ + n)  ∎

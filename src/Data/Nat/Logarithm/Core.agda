-----------------------------------------------------------------------
-- The Agda standard library
--
-- Logarithm base 2 core definitions and properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Logarithm.Core where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
open import Data.Unit

------------------------------------------------------------------------
-- Logarithm base 2

-- Floor version

⌊log2⌋ : ∀ n → Acc _<_ n → ℕ
⌊log2⌋ 0          _        = 0
⌊log2⌋ 1          _        = 0
⌊log2⌋ (suc n′@(suc n)) (acc rs) = 1 + ⌊log2⌋ (suc ⌊ n /2⌋) (rs _ (⌊n/2⌋<n n′))


-- Ceil version

⌈log2⌉ : ∀ n → Acc _<_ n → ℕ
⌈log2⌉ 0                _        = 0
⌈log2⌉ 1                _        = 0
⌈log2⌉ (suc (suc n)) (acc rs) = 1 + ⌈log2⌉ (suc ⌈ n /2⌉) (rs _ (⌈n/2⌉<n n))

------------------------------------------------------------------------
-- Properties of ⌊log2⌋

⌊log2⌋-acc-irrelevant : ∀ a {acc acc'} → ⌊log2⌋ a acc ≡ ⌊log2⌋ a acc'
⌊log2⌋-acc-irrelevant 0            {_}      {_}       = refl
⌊log2⌋-acc-irrelevant 1            {_}      {_}       = refl
⌊log2⌋-acc-irrelevant (suc (suc n)) {acc rs} {acc rs'} =
  cong suc (⌊log2⌋-acc-irrelevant (suc ⌊ n /2⌋))

⌊log2⌋-cong-irr : ∀ {a b} {acc acc'} → (p : a ≡ b) →
                ⌊log2⌋ a acc ≡ ⌊log2⌋ b acc'
⌊log2⌋-cong-irr {acc = ac} refl = ⌊log2⌋-acc-irrelevant _ {ac}

⌊log2⌋-mono-≤ : ∀ {a b} {acc acc'} → a ≤ b → ⌊log2⌋ a acc ≤ ⌊log2⌋ b acc'
⌊log2⌋-mono-≤ {_}           {_}     z≤n       = z≤n
⌊log2⌋-mono-≤ {_}           {_}     (s≤s z≤n) = z≤n
⌊log2⌋-mono-≤ {acc = acc _} {acc _} (s≤s (s≤s p)) =
  s≤s (⌊log2⌋-mono-≤ (⌊n/2⌋-mono (+-monoʳ-≤ 2 p)))

⌊log2⌋⌊n/2⌋≡⌊log2⌋n∸1 : ∀ n {acc} {acc'} →
                        ⌊log2⌋ ⌊ n /2⌋ acc ≡ ⌊log2⌋ n acc' ∸ 1
⌊log2⌋⌊n/2⌋≡⌊log2⌋n∸1 0             {_}      {_}       = refl
⌊log2⌋⌊n/2⌋≡⌊log2⌋n∸1 1             {_}      {_}       = refl
⌊log2⌋⌊n/2⌋≡⌊log2⌋n∸1 (suc (suc n)) {acc rs} {acc rs'} =
  ⌊log2⌋-acc-irrelevant (suc ⌊ n /2⌋)

⌊log2⌋2*b≡1+⌊log2⌋b : ∀ n {acc acc'} .{{ _ : NonZero n}} →
                      ⌊log2⌋ (2 * n) acc ≡ 1 + ⌊log2⌋ n acc'
⌊log2⌋2*b≡1+⌊log2⌋b (suc n) = begin
  ⌊log2⌋ (suc (n + suc (n + zero))) _              ≡⟨ ⌊log2⌋-cong-irr (cong (λ x → suc (n + suc x)) (+-comm n zero)) ⟩
  ⌊log2⌋ (suc (n + suc n)) (<-wellFounded _)       ≡⟨ ⌊log2⌋-cong-irr {acc' = <-wellFounded _} (cong suc (+-comm n (suc n))) ⟩
  ⌊log2⌋ (suc (suc n + n)) (<-wellFounded _)       ≡⟨ cong suc (⌊log2⌋-cong-irr {a = suc ⌊ n + n /2⌋} refl) ⟩
  suc (⌊log2⌋ (suc ⌊ n + n /2⌋) (<-wellFounded _)) ≡⟨ cong suc (⌊log2⌋-cong-irr (cong suc (sym (n≡⌊n+n/2⌋ n)))) ⟩
  suc (⌊log2⌋ (suc n) _)                           ∎
  where open ≡-Reasoning

⌊log2⌋2^n≡n : ∀ n {acc} → ⌊log2⌋ (2 ^ n) acc ≡ n
⌊log2⌋2^n≡n zero    = refl
⌊log2⌋2^n≡n (suc n) = begin
  ⌊log2⌋ ((2 ^ n) + ((2 ^ n) + zero)) _ ≡⟨ ⌊log2⌋2*b≡1+⌊log2⌋b (2 ^ n) {{m^n≢0 2 n}} ⟩
  1 + ⌊log2⌋ (2 ^ n) (<-wellFounded _)  ≡⟨ cong suc (⌊log2⌋2^n≡n n) ⟩
  suc n                                 ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of ⌈log2⌉

⌈log2⌉-acc-irrelevant : ∀ n {acc acc'} → ⌈log2⌉ n acc ≡ ⌈log2⌉ n acc'
⌈log2⌉-acc-irrelevant zero          {acc rs} {acc rs₁} = refl
⌈log2⌉-acc-irrelevant (suc zero)    {acc rs} {acc rs₁} = refl
⌈log2⌉-acc-irrelevant (suc (suc n)) {acc rs} {acc rs'} =
  cong suc (⌈log2⌉-acc-irrelevant (suc ⌊ suc n /2⌋))

⌈log2⌉-cong-irr : ∀ {m n} {acc acc'} → (_ : m ≡ n) →
                  ⌈log2⌉ m acc ≡ ⌈log2⌉ n acc'
⌈log2⌉-cong-irr {acc = ac} refl = ⌈log2⌉-acc-irrelevant _ {ac}

⌈log2⌉-mono-≤ : ∀ {m n} {acc acc'} → m ≤ n → ⌈log2⌉ m acc ≤ ⌈log2⌉ n acc'
⌈log2⌉-mono-≤ {_}            {_}       z≤n           = z≤n
⌈log2⌉-mono-≤ {_}            {_}       (s≤s z≤n)     = z≤n
⌈log2⌉-mono-≤ {acc = acc rs} {acc rs'} (s≤s (s≤s p)) =
  s≤s (⌈log2⌉-mono-≤ (⌈n/2⌉-mono (+-monoʳ-≤ 2 p)))

⌈log2⌉⌈n/2⌉≡⌈log2⌉n∸1 : ∀ n {acc} {acc'} →
                        ⌈log2⌉ ⌈ n /2⌉ acc ≡ ⌈log2⌉ n acc' ∸ 1
⌈log2⌉⌈n/2⌉≡⌈log2⌉n∸1 zero          {_}      {_}       = refl
⌈log2⌉⌈n/2⌉≡⌈log2⌉n∸1 (suc zero)    {_}      {_}       = refl
⌈log2⌉⌈n/2⌉≡⌈log2⌉n∸1 (suc (suc n)) {acc rs} {acc rs'} =
  ⌈log2⌉-acc-irrelevant (suc ⌊ suc n /2⌋)

⌈log2⌉2*n≡1+⌈log2⌉n : ∀ n {acc acc'} .{{_ : NonZero n}} →
                      ⌈log2⌉ (2 * n) acc ≡ 1 + ⌈log2⌉ n acc'
⌈log2⌉2*n≡1+⌈log2⌉n (suc n) = begin
  ⌈log2⌉ (suc (n + suc (n + zero))) _              ≡⟨ ⌈log2⌉-cong-irr (cong (λ x → suc (n + suc x)) (+-comm n zero)) ⟩
  ⌈log2⌉ (suc (n + suc n)) (<-wellFounded _)       ≡⟨ ⌈log2⌉-cong-irr {acc' = <-wellFounded _} (cong suc (+-comm n (suc n))) ⟩
  ⌈log2⌉ (suc (suc n + n)) (<-wellFounded _)       ≡⟨ cong suc (⌈log2⌉-cong-irr {m = suc ⌈ n + n /2⌉} refl) ⟩
  suc (⌈log2⌉ (suc ⌈ n + n /2⌉) (<-wellFounded _)) ≡⟨ cong suc (⌈log2⌉-cong-irr (cong suc (sym (n≡⌈n+n/2⌉ n)))) ⟩
  suc (⌈log2⌉ (suc n) _)                           ∎
  where open ≡-Reasoning

⌈log2⌉2^n≡n : ∀ n {acc} → ⌈log2⌉ (2 ^ n) acc ≡ n
⌈log2⌉2^n≡n zero    = refl
⌈log2⌉2^n≡n (suc n) = begin
  ⌈log2⌉ ((2 ^ n) + ((2 ^ n) + zero)) _ ≡⟨ ⌈log2⌉2*n≡1+⌈log2⌉n (2 ^ n) {{m^n≢0 2 n}} ⟩
  1 + ⌈log2⌉ (2 ^ n) (<-wellFounded _)  ≡⟨ cong suc (⌈log2⌉2^n≡n n) ⟩
  suc n                                 ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The Agda standard library
--
-- Component functions of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

module Data.Fin.Permutation.Components where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat as ℕ using (zero; suc; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties using (Involutive)
open ≡-Reasoning

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

-- 'tranpose i j' swaps the places of 'i' and 'j'.

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k with k ≟ i
... | yes _ = j
... | no  _ with k ≟ j
...   | yes _ = i
...   | no  _ = k

-- reverse i = n ∸ 1 ∸ i

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (ℕₚ.n∸m≤n (toℕ i) (suc n))

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

transpose-inverse : ∀ {n} (i j : Fin n) {k} →
                    transpose i j (transpose j i k) ≡ k
transpose-inverse i j {k} with k ≟ j
... | yes p rewrite ≡-≟-identity _≟_ {a = i} refl = sym p
... | no ¬p with k ≟ i
transpose-inverse i j {k} | no ¬p | yes q with j ≟ i
... | yes r = trans r (sym q)
... | no ¬r rewrite ≡-≟-identity _≟_ {a = j} refl = sym q
transpose-inverse i j {k} | no ¬p | no ¬q
  rewrite proj₂ (≢-≟-identity _≟_ ¬q)
        | proj₂ (≢-≟-identity _≟_ ¬p) = refl

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {zero} ()
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ inject≤-lemma _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎

reverse-involutive : ∀ {n} → Involutive _≡_ (reverse {n})
reverse-involutive {zero}  ()
reverse-involutive {suc n} i = toℕ-injective (begin
  toℕ (reverse (reverse i)) ≡⟨ reverse-prop (reverse i) ⟩
  n ∸ (toℕ (reverse i))     ≡⟨ cong (n ∸_) (reverse-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (ℕ.≤-pred (toℕ<n i)) ⟩
  toℕ i                     ∎)

reverse-suc : ∀ {n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n} {i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎

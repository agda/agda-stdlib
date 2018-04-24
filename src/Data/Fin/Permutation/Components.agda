------------------------------------------------------------------------
-- The Agda standard library
--
-- Components of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

module Data.Fin.Permutation.Components where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat as ℕ using (zero; suc; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans)
open import Algebra.FunctionProperties using (Involutive)

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

swap : ∀ {n} → Fin n → Fin n → Fin n → Fin n
swap i j k with k ≟ i
... | yes _ = j
... | no _ with k ≟ j
... | yes _ = i
... | no _ = k

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (ℕₚ.n∸m≤n (toℕ i) (suc n))

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

swap-inverse : ∀ {n} (i j : Fin n) {k} → swap i j (swap j i k) ≡ k
swap-inverse i j {k} with k ≟ j
... | yes p rewrite P.≡-≟-identity _≟_ {a = i} refl = sym p
... | no ¬p with k ≟ i
swap-inverse i j {k} | no ¬p | yes q with j ≟ i
... | yes r = trans r (sym q)
... | no ¬r rewrite P.≡-≟-identity _≟_ {a = j} refl = sym q
swap-inverse i j {k} | no ¬p | no ¬q
  rewrite proj₂ (P.≢-≟-identity _≟_ ¬q)
        | proj₂ (P.≢-≟-identity _≟_ ¬p) = refl

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {zero} ()
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ inject≤-lemma _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎
  where
  open P.≡-Reasoning

  toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
  toℕ‿ℕ- n       zero     = to-from n
  toℕ‿ℕ- zero    (suc ())
  toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

reverse-involutive : ∀ {n} → Involutive _≡_ (reverse {n})
reverse-involutive {zero}  ()
reverse-involutive {suc n} i = toℕ-injective (begin
  toℕ (reverse (reverse i)) ≡⟨ reverse-prop (reverse i) ⟩
  n ∸ (toℕ (reverse i))     ≡⟨ P.cong (n ∸_) (reverse-prop i) ⟩
  n ∸ (n ∸ (toℕ i))         ≡⟨ ℕₚ.m∸[m∸n]≡n (ℕ.≤-pred (bounded i)) ⟩
  toℕ i                     ∎)
  where open P.≡-Reasoning

reverse-suc : ∀ {n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n}{i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ P.sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎
  where
  open P.≡-Reasoning

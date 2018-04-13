------------------------------------------------------------------------
-- The Agda standard library
--
-- Bijections on finite sets, i.e. permutations.
------------------------------------------------------------------------

module Data.Fin.Permutation where

open import Data.Fin
open import Data.Fin.Properties

open import Data.Nat using (ℕ; suc; zero)
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; →-to-⟶; cong; cong₂; ≡-≟-identity; ≢-≟-identity; module ≡-Reasoning)
open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟨$⟩_)
open import Function using (_∘_)

open ≡-Reasoning

-- A permuation that swaps the two given indices.

swap-perm : ∀ {n} → Fin n → Fin n → Fin n ↔ Fin n
swap-perm {n} i j = record
  { to = →-to-⟶ (swap i j)
  ; from = →-to-⟶ (swap j i)
  ; inverse-of = record
    { left-inverse-of = λ _ → swap-inverse _ _
    ; right-inverse-of = λ _ → swap-inverse _ _
    }
  }

-- Given a permutation
--
-- [0 ↦ i₀, …, k ↦ iₖ, …, n ↦ iₙ]
--
-- yields a permutation
--
-- [0 ↦ i₀, …, k-1 ↦ i_{k-1}, k ↦ i_{k+1}, k+1 ↦ i_{k+2}, …, n-1 ↦ iₙ]
--
-- Intuitively, 'removeIn↔ k π' removes the element at index 'k' from the
-- permutation 'π'.

removeIn↔ : ∀ {m n} (i : Fin (suc m)) → Fin (suc m) ↔ Fin (suc n) → Fin m ↔ Fin n
removeIn↔ {m}{n} i π = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = left-inverse-of
    ; right-inverse-of = right-inverse-of
    }
  }
  where
  πʳ = Inverse.to π ⟨$⟩_
  πˡ = Inverse.from π ⟨$⟩_

  permute-≢ : ∀ {i j} → i ≢ j → πʳ i ≢ πʳ j
  permute-≢ p q = p (Inverse.injective π q)

  to-punchOut : ∀ {j : Fin m} → πʳ i ≢ πʳ (punchIn i j)
  to-punchOut = permute-≢ (i≢punchInᵢ _ _)

  from-punchOut : ∀ {j : Fin n} → i ≢ πˡ (punchIn (πʳ i) j)
  from-punchOut {j} p = i≢punchInᵢ (πʳ i) j (
    begin
      πʳ i                        ≡⟨ cong πʳ p ⟩
      πʳ (πˡ (punchIn (πʳ i) j))  ≡⟨ Inverse.right-inverse-of π _ ⟩
      punchIn (πʳ i) j            ∎)

  to : Fin m → Fin n
  to j = punchOut to-punchOut

  from : Fin n → Fin m
  from j = punchOut {j = πˡ (punchIn (πʳ i) j)} from-punchOut

  left-inverse-of : ∀ j → from (to j) ≡ j
  left-inverse-of j =
    begin
      from (to j)                                                      ≡⟨⟩
      punchOut {i = i} {πˡ (punchIn (πʳ i) (punchOut to-punchOut))} _  ≡⟨ punchOut-cong′ i (cong πˡ (punchIn-punchOut _)) ⟩
      punchOut {i = i} {πˡ (πʳ (punchIn i j))}                      _  ≡⟨ punchOut-cong i (Inverse.left-inverse-of π _) ⟩
      punchOut {i = i} {punchIn i j}                                _  ≡⟨ punchOut-punchIn i ⟩
      j                                                                ∎

  right-inverse-of : ∀ j → to (from j) ≡ j
  right-inverse-of j =
    begin
      to (from j)                                                      ≡⟨⟩
      punchOut {i = πʳ i} {πʳ (punchIn i (punchOut from-punchOut))} _  ≡⟨ punchOut-cong′ (πʳ i) (cong πʳ (punchIn-punchOut _)) ⟩
      punchOut {i = πʳ i} {πʳ (πˡ (punchIn (πʳ i) j))}              _  ≡⟨ punchOut-cong (πʳ i) (Inverse.right-inverse-of π _) ⟩
      punchOut {i = πʳ i} {punchIn (πʳ i) j}                        _  ≡⟨ punchOut-punchIn (πʳ i) ⟩
      j                                                                ∎

module _ {n} (π : Fin (suc n) ↔ Fin (suc n)) where
  private
    πʳ = Inverse.to π ⟨$⟩_
    πˡ = Inverse.from π ⟨$⟩_

  punchIn-permute : ∀ i j → πʳ (punchIn i j) ≡ punchIn (πʳ i) (Inverse.to (removeIn↔ i π) ⟨$⟩ j)
  punchIn-permute i j =
    begin
      πʳ (punchIn i j)                                             ≡⟨ sym (punchIn-punchOut _) ⟩
      punchIn (πʳ i) (punchOut {i = πʳ i} {πʳ (punchIn i j)} _)    ≡⟨⟩
      punchIn (πʳ i) (Inverse.to (removeIn↔ i π) ⟨$⟩ j)            ∎

  punchIn-permute′ : ∀ i j → πʳ (punchIn (πˡ i) j) ≡ punchIn i (Inverse.to (removeIn↔ (πˡ i) π) ⟨$⟩ j)
  punchIn-permute′ i j =
    begin
      πʳ (punchIn (πˡ i) j)                                         ≡⟨ punchIn-permute _ _ ⟩
      punchIn (πʳ (πˡ i)) (Inverse.to (removeIn↔ (πˡ i) π) ⟨$⟩ j)   ≡⟨ cong₂ punchIn (Inverse.right-inverse-of π i) refl ⟩
      punchIn i (Inverse.to (removeIn↔ (πˡ i) π) ⟨$⟩ j)             ∎

-- If there is a bijection between finite sets of size 'm' and 'n', then
-- 'm' = 'n'.

↔-≡ : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
↔-≡ {zero} {zero} p = refl
↔-≡ {zero} {suc n} p with Inverse.from p ⟨$⟩ zero
↔-≡ {zero} {suc n} p | ()
↔-≡ {suc m} {zero} p with Inverse.to p ⟨$⟩ zero
↔-≡ {suc m} {zero} p | ()
↔-≡ {suc m} {suc n} p = cong suc (↔-≡ (removeIn↔ zero p))

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
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; trans; sym; →-to-⟶; cong; cong₂)
open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟨$⟩_)
open import Function using (_∘_)

open P.≡-Reasoning

Permutation′ : ℕ → ℕ → Set
Permutation′ m n = Fin m ↔ Fin n

Permutation : ℕ → Set
Permutation n = Permutation′ n n

_⟨$⟩ʳ_ : ∀ {m n} → Permutation′ m n → Fin m → Fin n
_⟨$⟩ʳ_ = _⟨$⟩_ ∘ Inverse.to

_⟨$⟩ˡ_ : ∀ {m n} → Permutation′ m n → Fin n → Fin m
_⟨$⟩ˡ_ = _⟨$⟩_ ∘ Inverse.from

inverseˡ : ∀ {m n} (π : Permutation′ m n) {i} → π ⟨$⟩ˡ (π ⟨$⟩ʳ i) ≡ i
inverseˡ π = Inverse.left-inverse-of π _

inverseʳ : ∀ {m n} (π : Permutation′ m n) {i} → π ⟨$⟩ʳ (π ⟨$⟩ˡ i) ≡ i
inverseʳ π = Inverse.right-inverse-of π _

-- A permuation that swaps the two given indices.

swap : ∀ {n} → Fin n → Fin n → Permutation n
swap {n} i j = record
  { to = →-to-⟶ (swap′ i j)
  ; from = →-to-⟶ (swap′ j i)
  ; inverse-of = record
    { left-inverse-of = λ _ → inverse _ _
    ; right-inverse-of = λ _ → inverse _ _
    }
  }
  where
  swap′ : ∀ {n} → Fin n → Fin n → Fin n → Fin n
  swap′ i j k with k ≟ i
  ... | yes _ = j
  ... | no _ with k ≟ j
  ... | yes _ = i
  ... | no _ = k

  inverse : ∀ {n} (i j : Fin n) {k} → swap′ i j (swap′ j i k) ≡ k
  inverse i j {k} with k ≟ j
  ... | yes p rewrite P.≡-≟-identity _≟_ {a = i} refl = sym p
  ... | no ¬p with k ≟ i
  inverse i j {k} | no ¬p | yes q with j ≟ i
  ... | yes r = trans r (sym q)
  ... | no ¬r rewrite P.≡-≟-identity _≟_ {a = j} refl = sym q
  inverse i j {k} | no ¬p | no ¬q
    rewrite proj₂ (P.≢-≟-identity _≟_ ¬q)
          | proj₂ (P.≢-≟-identity _≟_ ¬p) = refl

-- Given a permutation
--
-- [0 ↦ i₀, …, k ↦ iₖ, …, n ↦ iₙ]
--
-- yields a permutation
--
-- [0 ↦ i₀, …, k-1 ↦ i_{k-1}, k ↦ i_{k+1}, k+1 ↦ i_{k+2}, …, n-1 ↦ iₙ]
--
-- Intuitively, 'removeMember k π' removes the element at index 'k' from the
-- permutation 'π'.

removeMember : ∀ {m n} (i : Fin (suc m)) → Permutation′ (suc m) (suc n) → Permutation′ m n
removeMember {m}{n} i π = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = left-inverse-of
    ; right-inverse-of = right-inverse-of
    }
  }
  where
  πʳ = π ⟨$⟩ʳ_
  πˡ = π ⟨$⟩ˡ_

  permute-≢ : ∀ {i j} → i ≢ j → πʳ i ≢ πʳ j
  permute-≢ p q = p (Inverse.injective π q)

  to-punchOut : ∀ {j : Fin m} → πʳ i ≢ πʳ (punchIn i j)
  to-punchOut = permute-≢ (i≢punchInᵢ _ _)

  from-punchOut : ∀ {j : Fin n} → i ≢ πˡ (punchIn (πʳ i) j)
  from-punchOut {j} p = i≢punchInᵢ (πʳ i) j (
    begin
      πʳ i                        ≡⟨ cong πʳ p ⟩
      πʳ (πˡ (punchIn (πʳ i) j))  ≡⟨ inverseʳ π ⟩
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
      punchOut {i = i} {πˡ (πʳ (punchIn i j))}                      _  ≡⟨ punchOut-cong i (inverseˡ π) ⟩
      punchOut {i = i} {punchIn i j}                                _  ≡⟨ punchOut-punchIn i ⟩
      j                                                                ∎

  right-inverse-of : ∀ j → to (from j) ≡ j
  right-inverse-of j =
    begin
      to (from j)                                                      ≡⟨⟩
      punchOut {i = πʳ i} {πʳ (punchIn i (punchOut from-punchOut))} _  ≡⟨ punchOut-cong′ (πʳ i) (cong πʳ (punchIn-punchOut _)) ⟩
      punchOut {i = πʳ i} {πʳ (πˡ (punchIn (πʳ i) j))}              _  ≡⟨ punchOut-cong (πʳ i) (inverseʳ π) ⟩
      punchOut {i = πʳ i} {punchIn (πʳ i) j}                        _  ≡⟨ punchOut-punchIn (πʳ i) ⟩
      j                                                                ∎

module _ {n} (π : Permutation (suc n)) where
  private
    πʳ = π ⟨$⟩ʳ_
    πˡ = π ⟨$⟩ˡ_

  punchIn-permute : ∀ i j → πʳ (punchIn i j) ≡ punchIn (πʳ i) (removeMember i π ⟨$⟩ʳ j)
  punchIn-permute i j =
    begin
      πʳ (punchIn i j)                                             ≡⟨ sym (punchIn-punchOut _) ⟩
      punchIn (πʳ i) (punchOut {i = πʳ i} {πʳ (punchIn i j)} _)    ≡⟨⟩
      punchIn (πʳ i) (removeMember i π ⟨$⟩ʳ j)                     ∎

  punchIn-permute′ : ∀ i j → πʳ (punchIn (πˡ i) j) ≡ punchIn i (removeMember (πˡ i) π ⟨$⟩ʳ j)
  punchIn-permute′ i j =
    begin
      πʳ (punchIn (πˡ i) j)                                ≡⟨ punchIn-permute _ _ ⟩
      punchIn (πʳ (πˡ i)) (removeMember (πˡ i) π ⟨$⟩ʳ j)   ≡⟨ cong₂ punchIn (inverseʳ π) refl ⟩
      punchIn i (removeMember (πˡ i) π ⟨$⟩ʳ j)             ∎

-- If there is a bijection between finite sets of size 'm' and 'n', then
-- 'm' = 'n'.

↔-≡ : ∀ {m n} → Permutation′ m n → m ≡ n
↔-≡ {zero} {zero} π = refl
↔-≡ {zero} {suc n} π with π ⟨$⟩ˡ zero
↔-≡ {zero} {suc n} π | ()
↔-≡ {suc m} {zero} π with π ⟨$⟩ʳ zero
↔-≡ {suc m} {zero} π | ()
↔-≡ {suc m} {suc n} π = cong suc (↔-≡ (removeMember zero π))

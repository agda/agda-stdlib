------------------------------------------------------------------------
-- The Agda standard library
--
-- Bijections on finite sets (i.e. permutations).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Permutation where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Fin.Properties
import Data.Fin.Permutation.Components as PC
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product using (proj₂)
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (does; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; trans; sym; →-to-⟶; cong; cong₂)
open P.≡-Reasoning

private
  variable
    m n o : ℕ

------------------------------------------------------------------------
-- Types

-- A bijection between finite sets of potentially different sizes.
-- There only exist inhabitants of this type if in fact m = n, however
-- it is often easier to prove the existence of a bijection without
-- first proving that the sets have the same size. Indeed such a
-- bijection is a useful way to prove that the sets are in fact the same
-- size. See '↔-≡' below.

Permutation : ℕ → ℕ → Set
Permutation m n = Fin m ↔ Fin n

Permutation′ : ℕ → Set
Permutation′ n = Permutation n n

------------------------------------------------------------------------
-- Helper functions

permutation : ∀ (f : Fin m → Fin n) (g : Fin n → Fin m) →
              (→-to-⟶ g) InverseOf (→-to-⟶ f) → Permutation m n
permutation f g inv = record
  { to         = →-to-⟶ f
  ; from       = →-to-⟶ g
  ; inverse-of = inv
  }

infixl 5 _⟨$⟩ʳ_ _⟨$⟩ˡ_
_⟨$⟩ʳ_ : Permutation m n → Fin m → Fin n
_⟨$⟩ʳ_ = _⟨$⟩_ ∘ Inverse.to

_⟨$⟩ˡ_ : Permutation m n → Fin n → Fin m
_⟨$⟩ˡ_ = _⟨$⟩_ ∘ Inverse.from

inverseˡ : ∀ (π : Permutation m n) {i} → π ⟨$⟩ˡ (π ⟨$⟩ʳ i) ≡ i
inverseˡ π = Inverse.left-inverse-of π _

inverseʳ : ∀ (π : Permutation m n) {i} → π ⟨$⟩ʳ (π ⟨$⟩ˡ i) ≡ i
inverseʳ π = Inverse.right-inverse-of π _

------------------------------------------------------------------------
-- Equality

infix 6 _≈_
_≈_ : Rel (Permutation m n) 0ℓ
π ≈ ρ = ∀ i → π ⟨$⟩ʳ i ≡ ρ ⟨$⟩ʳ i

------------------------------------------------------------------------
-- Example permutations

-- Identity

id : Permutation′ n
id = Inverse.id

-- Transpose two indices

transpose : Fin n → Fin n → Permutation′ n
transpose i j = permutation (PC.transpose i j) (PC.transpose j i) record
  { left-inverse-of  = λ _ → PC.transpose-inverse _ _
  ; right-inverse-of = λ _ → PC.transpose-inverse _ _
  }

-- Reverse the order of indices

reverse : Permutation′ n
reverse = permutation PC.reverse PC.reverse record
  { left-inverse-of  = PC.reverse-involutive
  ; right-inverse-of = PC.reverse-involutive
  }

------------------------------------------------------------------------
-- Operations

-- Composition

infixr 9 _∘ₚ_
_∘ₚ_ : Permutation m n → Permutation n o → Permutation m o
π₁ ∘ₚ π₂ = π₂ Inverse.∘ π₁

-- Flip

flip : Permutation m n → Permutation n m
flip = Inverse.sym

-- Element removal
--
-- `remove k [0 ↦ i₀, …, k ↦ iₖ, …, n ↦ iₙ]` yields
--
-- [0 ↦ i₀, …, k-1 ↦ iₖ₋₁, k ↦ iₖ₊₁, k+1 ↦ iₖ₊₂, …, n-1 ↦ iₙ]

remove : Fin (suc m) → Permutation (suc m) (suc n) → Permutation m n
remove {m} {n} i π = permutation to from record
  { left-inverse-of  = left-inverse-of
  ; right-inverse-of = right-inverse-of
  }
  where
  πʳ = π ⟨$⟩ʳ_
  πˡ = π ⟨$⟩ˡ_

  permute-≢ : ∀ {i j} → i ≢ j → πʳ i ≢ πʳ j
  permute-≢ p = p ∘ (Inverse.injective π)

  to-punchOut : ∀ {j : Fin m} → πʳ i ≢ πʳ (punchIn i j)
  to-punchOut = permute-≢ (punchInᵢ≢i _ _ ∘ sym)

  from-punchOut : ∀ {j : Fin n} → i ≢ πˡ (punchIn (πʳ i) j)
  from-punchOut {j} p = punchInᵢ≢i (πʳ i) j (sym (begin
    πʳ i                        ≡⟨ cong πʳ p ⟩
    πʳ (πˡ (punchIn (πʳ i) j))  ≡⟨ inverseʳ π ⟩
    punchIn (πʳ i) j            ∎))

  to : Fin m → Fin n
  to j = punchOut (to-punchOut {j})

  from : Fin n → Fin m
  from j = punchOut {j = πˡ (punchIn (πʳ i) j)} from-punchOut

  left-inverse-of : ∀ j → from (to j) ≡ j
  left-inverse-of j = begin
    from (to j)                                                      ≡⟨⟩
    punchOut {i = i} {πˡ (punchIn (πʳ i) (punchOut to-punchOut))} _  ≡⟨ punchOut-cong′ i (cong πˡ (punchIn-punchOut _)) ⟩
    punchOut {i = i} {πˡ (πʳ (punchIn i j))}                      _  ≡⟨ punchOut-cong i (inverseˡ π) ⟩
    punchOut {i = i} {punchIn i j}                                _  ≡⟨ punchOut-punchIn i ⟩
    j                                                                ∎

  right-inverse-of : ∀ j → to (from j) ≡ j
  right-inverse-of j = begin
    to (from j)                                                       ≡⟨⟩
    punchOut {i = πʳ i} {πʳ (punchIn i (punchOut from-punchOut))}  _  ≡⟨ punchOut-cong′ (πʳ i) (cong πʳ (punchIn-punchOut _)) ⟩
    punchOut {i = πʳ i} {πʳ (πˡ (punchIn (πʳ i) j))}               _  ≡⟨ punchOut-cong (πʳ i) (inverseʳ π) ⟩
    punchOut {i = πʳ i} {punchIn (πʳ i) j}                         _  ≡⟨ punchOut-punchIn (πʳ i) ⟩
    j                                                                 ∎

-- lift: takes a permutation m → n and creates a permutation (suc m) → (suc n)
-- by mapping 0 to 0 and applying the input permutation to everything else
lift₀ : Permutation m n → Permutation (suc m) (suc n)
lift₀ {m} {n} π = permutation to from record
  { left-inverse-of = left-inverse-of
  ; right-inverse-of = right-inverse-of
  }
  where
  to : Fin (suc m) → Fin (suc n)
  to 0F      = 0F
  to (suc i) = suc (π ⟨$⟩ʳ i)

  from : Fin (suc n) → Fin (suc m)
  from 0F      = 0F
  from (suc i) = suc (π ⟨$⟩ˡ i)

  left-inverse-of : ∀ j → from (to j) ≡ j
  left-inverse-of 0F      = refl
  left-inverse-of (suc j) = cong suc (inverseˡ π)

  right-inverse-of : ∀ j → to (from j) ≡ j
  right-inverse-of 0F      = refl
  right-inverse-of (suc j) = cong suc (inverseʳ π)

------------------------------------------------------------------------
-- Other properties

module _ (π : Permutation (suc m) (suc n)) where
  private
    πʳ = π ⟨$⟩ʳ_
    πˡ = π ⟨$⟩ˡ_

  punchIn-permute : ∀ i j → πʳ (punchIn i j) ≡ punchIn (πʳ i) (remove i π ⟨$⟩ʳ j)
  punchIn-permute i j = sym (punchIn-punchOut _)

  punchIn-permute′ : ∀ i j → πʳ (punchIn (πˡ i) j) ≡ punchIn i (remove (πˡ i) π ⟨$⟩ʳ j)
  punchIn-permute′ i j = begin
    πʳ (punchIn (πˡ i) j)                         ≡⟨ punchIn-permute _ _ ⟩
    punchIn (πʳ (πˡ i)) (remove (πˡ i) π ⟨$⟩ʳ j)  ≡⟨ cong₂ punchIn (inverseʳ π) refl ⟩
    punchIn i (remove (πˡ i) π ⟨$⟩ʳ j)            ∎

  lift₀-remove : πʳ 0F ≡ 0F → lift₀ (remove 0F π) ≈ π
  lift₀-remove p 0F      = sym p
  lift₀-remove p (suc i) = punchOut-zero (πʳ (suc i)) p
    where
    punchOut-zero : ∀ {i} (j : Fin (suc n)) {neq} → i ≡ 0F → suc (punchOut {i = i} {j} neq) ≡ j
    punchOut-zero 0F {neq} p = ⊥-elim (neq p)
    punchOut-zero (suc j) refl = refl

↔⇒≡ : Permutation m n → m ≡ n
↔⇒≡ {zero}  {zero}  π = refl
↔⇒≡ {zero}  {suc n} π = contradiction (π ⟨$⟩ˡ 0F) ¬Fin0
↔⇒≡ {suc m} {zero}  π = contradiction (π ⟨$⟩ʳ 0F) ¬Fin0
↔⇒≡ {suc m} {suc n} π = cong suc (↔⇒≡ (remove 0F π))

fromPermutation : Permutation m n → Permutation′ m
fromPermutation π = P.subst (Permutation _) (sym (↔⇒≡ π)) π

refute : m ≢ n → ¬ Permutation m n
refute m≢n π = contradiction (↔⇒≡ π) m≢n

lift₀-id : (i : Fin (suc n)) → lift₀ id ⟨$⟩ʳ i ≡ i
lift₀-id 0F      = refl
lift₀-id (suc i) = refl

lift₀-comp : ∀ (π : Permutation m n) (ρ : Permutation n o) →
             lift₀ π ∘ₚ lift₀ ρ ≈ lift₀ (π ∘ₚ ρ)
lift₀-comp π ρ 0F      = refl
lift₀-comp π ρ (suc i) = refl

lift₀-cong : ∀ (π ρ : Permutation m n) → π ≈ ρ → lift₀ π ≈ lift₀ ρ
lift₀-cong π ρ f 0F      = refl
lift₀-cong π ρ f (suc i) = cong suc (f i)

lift₀-transpose : ∀ (i j : Fin n) → transpose (suc i) (suc j) ≈ lift₀ (transpose i j)
lift₀-transpose i j 0F      = refl
lift₀-transpose i j (suc k) with does (k ≟ i)
... | true = refl
... | false with does (k ≟ j)
...   | false = refl
...   | true = refl

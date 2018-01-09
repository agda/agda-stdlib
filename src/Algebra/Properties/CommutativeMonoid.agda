------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.CommutativeMonoid {g₁ g₂} (M : CommutativeMonoid g₁ g₂) where

open CommutativeMonoid M renaming (ε to 0#; _∙_ to _+_; ∙-cong to +-cong; identity to +-identity; assoc to +-assoc; comm to +-comm)
open import Algebra.Operations.CommutativeMonoid M
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (Inverse; _↔_)
open import Data.Product
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; punchIn)
open import Data.Fin.Properties as FP using (removeIn↔; punchIn-permute′; swapFin)
open import Data.Fin.Vec using (select; select-const)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- When summing over a function from a finite set, we can pull out any value and move it to the front.
sumFin-punchIn : ∀ {n} f (i : Fin (ℕ.suc n)) → sumFin (ℕ.suc n) f ≈ f i + sumFin n (f ∘ punchIn i)
sumFin-punchIn f Fin.zero = refl
sumFin-punchIn {ℕ.zero} f (Fin.suc ())
sumFin-punchIn {ℕ.suc n} f (Fin.suc i) =
  begin
    f Fin.zero + (sumFin (ℕ.suc n) (f ∘ Fin.suc))                       ≈⟨ +-cong refl (sumFin-punchIn (f ∘ Fin.suc) i) ⟩
    f Fin.zero + (f (Fin.suc i) + sumFin n (f ∘ Fin.suc ∘ punchIn i))   ≈⟨ sym (+-assoc _ _ _) ⟩
    (f Fin.zero + f (Fin.suc i)) + sumFin n (f ∘ Fin.suc ∘ punchIn i)   ≈⟨ +-cong (+-comm _ _) refl ⟩
    (f (Fin.suc i) + f Fin.zero) + sumFin n (f ∘ Fin.suc ∘ punchIn i)   ≈⟨ +-assoc _ _ _ ⟩
    f (Fin.suc i) + (f Fin.zero + sumFin n (f ∘ Fin.suc ∘ punchIn i))   ∎

-- '_≈_' is a congruence over 'sum n'.
sumFin-cong : ∀ {n f g} → (∀ i → f i ≈ g i) → sumFin n f ≈ sumFin n g
sumFin-cong {ℕ.zero} p = refl
sumFin-cong {ℕ.suc n} p = +-cong (p _) (sumFin-cong (p ∘ Fin.suc))

-- '_≡_' is a congruence over 'sum n'.
sumFin-cong≡ : ∀ {n f g} → (∀ i → f i ≡ g i) → sumFin n f ≡ sumFin n g
sumFin-cong≡ {ℕ.zero} p = PE.refl
sumFin-cong≡ {ℕ.suc n} p = PE.cong₂ _+_ (p _) (sumFin-cong≡ (p ∘ Fin.suc))

-- The sumFin over the constantly zero function is zero.
sumFin-zero : ∀ n → sumFin n (λ _ → 0#) ≈ 0#
sumFin-zero (ℕ.zero) = refl
sumFin-zero (ℕ.suc n) =
  begin
    0# + sumFin n (λ _ → 0#)   ≈⟨ proj₁ +-identity _ ⟩
    sumFin n (λ _ → 0#)        ≈⟨ sumFin-zero n ⟩
    0#                         ∎

-- The 'sum' operator distributes over addition.
sumFin-+-hom : ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i + ∑[ i < n ] g i ≈ ∑[ i < n ] (f i + g i)
sumFin-+-hom ℕ.zero f g = proj₁ +-identity _
sumFin-+-hom (ℕ.suc n) f g =
  let fz = f Fin.zero
      gz = g Fin.zero
      ∑f  = ∑[ i < n ] f (Fin.suc i)
      ∑g  = ∑[ i < n ] g (Fin.suc i)
      ∑fg = ∑[ i < n ] (f (Fin.suc i) + g (Fin.suc i))
  in begin
    (fz + ∑f) + (gz + ∑g)      ≈⟨ +-assoc _ _ _ ⟩
    fz + (∑f + (gz + ∑g))      ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
    fz + ((∑f + gz) + ∑g)      ≈⟨ +-cong refl (+-cong (+-comm _ _) refl) ⟩
    fz + ((gz + ∑f) + ∑g)      ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
    fz + (gz + (∑f + ∑g))      ≈⟨ +-cong refl (+-cong refl (sumFin-+-hom n _ _)) ⟩
    fz + (gz + ∑fg)            ≈⟨ sym (+-assoc _ _ _) ⟩
    fz + gz + ∑fg              ∎

-- The 'sum' operator commutes with itself.
sumFin-comm : ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
sumFin-comm ℕ.zero m f = sym (sumFin-zero m)
sumFin-comm (ℕ.suc n) m f =
  begin
    ∑[ j < m ] f Fin.zero j + ∑[ i < n ] ∑[ j < m ] f (Fin.suc i) j   ≈⟨ +-cong refl (sumFin-comm n m _) ⟩
    ∑[ j < m ] f Fin.zero j + ∑[ j < m ] ∑[ i < n ] f (Fin.suc i) j   ≈⟨ sumFin-+-hom m _ _ ⟩
    ∑[ j < m ] (f Fin.zero j + ∑[ i < n ] f (Fin.suc i) j)            ∎

-- Any permutation of a vector has the same sumFin as the original.

sumFin-permute : ∀ {n} (f : Fin n → Carrier) (π : Fin n ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (Inverse.to π ⟨$⟩ i)
sumFin-permute {ℕ.zero} _ π = refl
sumFin-permute {ℕ.suc n} f π =
  begin
    sumFin (ℕ.suc n) f                                                                          ≡⟨⟩
    f 0i + sumFin n (f ∘ punchIn 0i)                                                            ≈⟨ +-cong refl (sumFin-permute _ (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π)) ⟩
    f 0i + sumFin n (f ∘ punchIn 0i ∘ (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π) ⟨$⟩_))  ≡⟨ PE.cong₂ _+_ PE.refl (sumFin-cong≡ (PE.cong f ∘ PE.sym ∘ punchIn-permute′ π 0i)) ⟩
    f 0i + sumFin n (f ∘ (Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i))                 ≡⟨ PE.cong₂ _+_ (PE.cong f (PE.sym (Inverse.right-inverse-of π _))) PE.refl ⟩
    f _  + sumFin n (f ∘ (Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i))                 ≈⟨ sym (sumFin-punchIn (f ∘ (Inverse.to π ⟨$⟩_)) (Inverse.from π ⟨$⟩ 0i)) ⟩
    sumFin (ℕ.suc n) (f ∘ (Inverse.to π ⟨$⟩_))                                                  ∎
  where
    0i = Fin.zero
    ππ0 = Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ 0i)

-- A version of 'sumFin-permute' allowing heterogeneous sum lengths.

sumFin-permute′ : ∀ {m n} (f : Fin n → Carrier) (π : Fin m ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (Inverse.to π ⟨$⟩ i)
sumFin-permute′ f π with FP.↔-≡ π
sumFin-permute′ f π | PE.refl = sumFin-permute f π

-- If the function takes the same value at 'i' and 'j', then swapping 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.
select-swap : ∀ {n} f (i j : Fin n) → f i ≈ f j → ∀ k → (select 0# j f ∘ swapFin i j) k ≈ select 0# i f k
select-swap _ i j e k with k FP.≟ j
select-swap _ i j e k | yes p with k FP.≟ i
select-swap _ .k .k e k | yes PE.refl | yes PE.refl = reflexive (FP.if-dec-true k k PE.refl)
select-swap _ i .k e k | yes PE.refl | no ¬q = reflexive (FP.if-dec-false i k (¬q ∘ PE.sym))
select-swap _ i j e k | no ¬p with k FP.≟ i
select-swap f i j e k | no ¬p | yes q =
  begin
    (if ⌊ j FP.≟ j ⌋ then f j else 0#)    ≡⟨ FP.if-dec-true j j PE.refl ⟩
    f j                                   ≈⟨ sym e ⟩
    f i                                   ∎
select-swap _ i j e k | no ¬p | no ¬q = reflexive (FP.if-dec-false k j ¬p)

-- Summing over a pulse gives you the single value picked out by the pulse.
select-sum : ∀ {n i} f → sumFin n (select 0# i f) ≈ f i
select-sum {ℕ.zero} {()} f
select-sum {ℕ.suc n} {i} f =
  begin
    sumFin _ (select 0# i f)                                               ≈⟨ sumFin-permute (select 0# i f) (FP.swapIndices Fin.zero i) ⟩
    sumFin _ (select 0# i f ∘ swapFin Fin.zero i)                          ≡⟨ sumFin-cong≡ (select-const 0# i f ∘ swapFin Fin.zero i) ⟩
    sumFin (ℕ.suc n) (select 0# i (λ _ → f i) ∘ swapFin Fin.zero i)        ≈⟨ sumFin-cong (select-swap (λ _ → f i) Fin.zero i refl) ⟩
    sumFin (ℕ.suc n) (select 0# Fin.zero (λ _ → f i))                      ≡⟨⟩
    f i + sumFin n (λ _ → 0#)                                              ≈⟨ +-cong refl (sumFin-zero n) ⟩
    f i + 0#                                                               ≈⟨ proj₂ +-identity _ ⟩
    f i                                                                    ∎

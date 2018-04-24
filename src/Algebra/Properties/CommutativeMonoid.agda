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
import Relation.Binary as B
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (Inverse; _↔_)
open import Data.Product
import Data.Bool as Bool
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; punchIn)
import Data.List as List
open import Data.Fin.Properties as FP using (removeIn↔; punchIn-permute′; swapFin)
open import Data.Table as Table
open import Data.Table.Relation.Equality as TE using (_≗_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
import Data.Table.Properties as TP
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

module _ {n} where
  open B.Setoid (TE.setoid setoid n) public
    using ()
    renaming (_≈_ to _≋_)

-- When summing over a function from a finite set, we can pull out any value and move it to the front.
sumₜ-punchIn : ∀ {n} t (i : Fin (ℕ.suc n)) → sumₜ t ≈ lookup t i + sumₜ (rearrange (punchIn i) t)
sumₜ-punchIn f Fin.zero = refl
sumₜ-punchIn {ℕ.zero} t (Fin.suc ())
sumₜ-punchIn {ℕ.suc n} t (Fin.suc i) =
  begin
    head t + sumₜ (tail t)                                                    ≈⟨ +-cong refl (sumₜ-punchIn (tail t) i) ⟩
    head t + (lookup t (Fin.suc i) + sumₜ (rearrange (punchIn i) (tail t)))   ≈⟨ sym (+-assoc _ _ _) ⟩
    (head t + lookup t (Fin.suc i)) + sumₜ (rearrange (punchIn i) (tail t))   ≈⟨ +-cong (+-comm _ _) refl ⟩
    (lookup t (Fin.suc i) + head t) + sumₜ (rearrange (punchIn i) (tail t))   ≈⟨ +-assoc _ _ _ ⟩
    lookup t (Fin.suc i) + (head t + sumₜ (rearrange (punchIn i) (tail t)))   ∎

-- '_≈_' is a congruence over 'sumₜ n'.
sumₜ-cong : ∀ {n} {t t′ : Table Carrier n} → t ≋ t′ → sumₜ t ≈ sumₜ t′
sumₜ-cong {ℕ.zero} p = refl
sumₜ-cong {ℕ.suc n} p = +-cong (p _) (sumₜ-cong (p ∘ Fin.suc))

-- '_≡_' is a congruence over 'sum n'.
sumₜ-cong≡ : ∀ {n} {t t′ : Table Carrier n} → t ≗ t′ → sumₜ t ≡ sumₜ t′
sumₜ-cong≡ {ℕ.zero} p = PE.refl
sumₜ-cong≡ {ℕ.suc n} p = PE.cong₂ _+_ (p _) (sumₜ-cong≡ (p ∘ Fin.suc))

-- The sumₜ over the constantly zero function is zero.
sumₜ-zero : ∀ n → sumₜ (replicate {n} 0#) ≈ 0#
sumₜ-zero (ℕ.zero) = refl
sumₜ-zero (ℕ.suc n) =
  begin
    0# + sumₜ (replicate {n} 0#)  ≈⟨ proj₁ +-identity _ ⟩
    sumₜ (replicate {n} 0#)       ≈⟨ sumₜ-zero n ⟩
    0#                                ∎

-- The '∑' operator distributes over addition.
∑-+-hom : ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i + ∑[ i < n ] g i ≈ ∑[ i < n ] (f i + g i)
∑-+-hom ℕ.zero f g = proj₁ +-identity _
∑-+-hom (ℕ.suc n) f g =
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
    fz + (gz + (∑f + ∑g))      ≈⟨ +-cong refl (+-cong refl (∑-+-hom n _ _)) ⟩
    fz + (gz + ∑fg)            ≈⟨ sym (+-assoc _ _ _) ⟩
    fz + gz + ∑fg              ∎

-- The '∑' operator commutes with itself.
∑-comm : ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
∑-comm ℕ.zero m f = sym (sumₜ-zero m)
∑-comm (ℕ.suc n) m f =
  begin
    ∑[ j < m ] f Fin.zero j + ∑[ i < n ] ∑[ j < m ] f (Fin.suc i) j   ≈⟨ +-cong refl (∑-comm n m _) ⟩
    ∑[ j < m ] f Fin.zero j + ∑[ j < m ] ∑[ i < n ] f (Fin.suc i) j   ≈⟨ ∑-+-hom m _ _ ⟩
    ∑[ j < m ] (f Fin.zero j + ∑[ i < n ] f (Fin.suc i) j)            ∎

-- Any permutation of a table has the same sum as the original.

sumₜ-permute : ∀ {n} t (π : Fin n ↔ Fin n) → sumₜ t ≈ sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)
sumₜ-permute {ℕ.zero} t π = refl
sumₜ-permute {ℕ.suc n} t π =
  let f = lookup t
  in
  begin
    sumₜ t                                                                                            ≡⟨⟩
    f 0i + sumₜ (rearrange (punchIn 0i) t)                                                            ≈⟨ +-cong refl (sumₜ-permute _ (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π)) ⟩
    f 0i + sumₜ (rearrange (punchIn 0i ∘ (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π) ⟨$⟩_)) t)  ≡⟨ PE.cong₂ _+_ PE.refl (sumₜ-cong≡ (PE.cong f ∘ PE.sym ∘ punchIn-permute′ π 0i)) ⟩
    f 0i + sumₜ (rearrange ((Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i)) t)                 ≡⟨ PE.cong₂ _+_ (PE.cong f (PE.sym (Inverse.right-inverse-of π _))) PE.refl ⟩
    f _  + sumₜ (rearrange ((Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i)) t)                 ≈⟨ sym (sumₜ-punchIn (rearrange (Inverse.to π ⟨$⟩_) t) (Inverse.from π ⟨$⟩ 0i)) ⟩
    sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)                                                            ∎
  where
    0i = Fin.zero
    ππ0 = Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ 0i)

-- A version of 'sumₜ-permute' allowing heterogeneous sum lengths.

sumₜ-permute′ : ∀ {m n} t (π : Fin m ↔ Fin n) → sumₜ t ≈ sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)
sumₜ-permute′ t π with FP.↔-≡ π
sumₜ-permute′ t π | PE.refl = sumₜ-permute t π

∑-permute : ∀ {n} (f : Fin n → Carrier) (π : Fin n ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (Inverse.to π ⟨$⟩ i)
∑-permute = sumₜ-permute ∘ tabulate

∑-permute′ : ∀ {m n} (f : Fin n → Carrier) (π : Fin m ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (Inverse.to π ⟨$⟩ i)
∑-permute′ = sumₜ-permute′ ∘ tabulate

private
  ⌊i≟i⌋ : ∀ {n} (i : Fin n) → ⌊ i FP.≟ i ⌋ ≡ Bool.true
  ⌊i≟i⌋ i with i FP.≟ i
  ⌊i≟i⌋ i | yes p = PE.refl
  ⌊i≟i⌋ i | no ¬p = ⊥-elim (¬p PE.refl)

-- If the function takes the same value at 'i' and 'j', then swapping 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.

select-swap : ∀ {n} t (i j : Fin n) → lookup t i ≈ lookup t j → ∀ k → (lookup (select 0# j t) ∘ swapFin i j) k ≈ lookup (select 0# i t) k
select-swap _ i j e k with k FP.≟ j
select-swap _ i j e k | yes p with k FP.≟ i
select-swap _ .k .k e k | yes PE.refl | yes PE.refl rewrite ⌊i≟i⌋ k = refl
select-swap _ i .k e k | yes PE.refl | no ¬q with i FP.≟ k
select-swap _ i .k e k | yes PE.refl | no ¬q | yes p = ⊥-elim (¬q (PE.sym p))
select-swap _ i .k e k | yes PE.refl | no ¬q | no ¬p = refl
select-swap _ i j e k | no ¬p with k FP.≟ i
select-swap t i j e k | no ¬p | yes q rewrite ⌊i≟i⌋ j = sym e
select-swap _ i j e k | no ¬p | no ¬q with k FP.≟ j
select-swap _ i j e k | no ¬p | no ¬q | yes p = ⊥-elim (¬p p)
select-swap _ i j e k | no ¬p | no ¬q | no ¬r = refl

-- Summing over a pulse gives you the single value picked out by the pulse.

select-sum : ∀ {n i} (t : Table Carrier n) → sumₜ (select 0# i t) ≈ lookup t i
select-sum {ℕ.zero} {()} t
select-sum {ℕ.suc n} {i} t =
  let f = lookup t
  in
  begin
    sumₜ (select 0# i t)                                                    ≈⟨ sumₜ-permute (select 0# i t) (FP.swapIndices Fin.zero i) ⟩
    sumₜ (rearrange (swapFin Fin.zero i) (select 0# i t))                   ≡⟨ sumₜ-cong≡ (TP.select-const 0# i t ∘ swapFin Fin.zero i) ⟩
    sumₜ (rearrange (swapFin Fin.zero i) (select 0# i (replicate (f i))))   ≈⟨ sumₜ-cong (select-swap (replicate (f i)) Fin.zero i refl) ⟩
    sumₜ (select 0# Fin.zero (replicate {ℕ.suc n} (f i)))                   ≡⟨⟩
    f i + sumₜ (replicate {n} 0#)                                           ≈⟨ +-cong refl (sumₜ-zero n) ⟩
    f i + 0#                                                                    ≈⟨ proj₂ +-identity _ ⟩
    f i                                                                         ∎

sumₜ-fromList : ∀ xs → sumₜ (fromList xs) ≡ sumₗ xs
sumₜ-fromList List.[] = PE.refl
sumₜ-fromList (x List.∷ xs) = PE.cong₂ _+_ PE.refl (sumₜ-fromList xs)

sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (toList t)
sumₜ-toList {ℕ.zero} _ = PE.refl
sumₜ-toList {ℕ.suc n} _ = PE.cong₂ _+_ PE.refl (sumₜ-toList {n} _)


sumₜ-idem-replicate : ∀ n {x : Carrier} → _+_ IdempotentOn x → sumₜ (Table.replicate {ℕ.suc n} x) ≈ x
sumₜ-idem-replicate ℕ.zero idem = proj₂ +-identity _
sumₜ-idem-replicate (ℕ.suc n) {x} idem = begin
  x + (x + sumₜ (Table.replicate {n} x))   ≈⟨ sym (+-assoc _ _ _) ⟩
  (x + x) + sumₜ (Table.replicate {n} x)   ≈⟨ +-cong idem refl ⟩
  x + sumₜ (Table.replicate {n} x)         ≈⟨ sumₜ-idem-replicate n idem ⟩
  x ∎

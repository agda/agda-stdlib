------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.CommutativeMonoid {g₁ g₂} (M : CommutativeMonoid g₁ g₂) where

open import Algebra.Operations.CommutativeMonoid M
open import Algebra.CommutativeMonoidSolver M
import Algebra.FunctionProperties as Props
import Relation.Binary.EqReasoning as EqR
import Relation.Binary as B
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; punchIn; zero; suc)
open import Data.List as List using ([]; _∷_)
import Data.Fin.Properties as FP
open import Data.Fin.Permutation as Perm using (Permutation; Permutation′; _⟨$⟩ˡ_; _⟨$⟩ʳ_)
open import Data.Fin.Permutation.Components as PermC
open import Data.Table as Table
open import Data.Table.Relation.Equality as TE using (_≗_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
import Data.Table.Properties as TP
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open CommutativeMonoid M
  renaming
  ( ε to 0#
  ; _∙_ to _+_
  ; ∙-cong to +-cong
  ; identity to +-identity
  ; assoc to +-assoc
  ; comm to +-comm
  )
open Props _≈_
open EqR setoid

module _ {n} where
  open B.Setoid (TE.setoid setoid n) public
    using ()
    renaming (_≈_ to _≋_)

-- When summing over a function from a finite set, we can pull out any value and move it to the front.

sumₜ-punchIn : ∀ {n} t (i : Fin (suc n)) → sumₜ t ≈ lookup t i + sumₜ (rearrange (punchIn i) t)
sumₜ-punchIn f zero = refl
sumₜ-punchIn {zero} t (suc ())
sumₜ-punchIn {suc n} t (suc i) =
  begin
    x + sumₜ (tail t)  ≈⟨ +-cong refl (sumₜ-punchIn (tail t) i) ⟩
    x + (y + z)        ≈⟨ solve 3 (λ x y z → x ⊕ (y ⊕ z) ⊜ y ⊕ (x ⊕ z)) refl x y z ⟩
    y + (x + z)        ∎
  where
  x = head t
  y = lookup t (suc i)
  z = sumₜ (rearrange (punchIn i) (tail t))

-- '_≈_' is a congruence over 'sumTable n'.

sumₜ-cong-≈ : ∀ {n} {t t′ : Table Carrier n} → t ≋ t′ → sumₜ t ≈ sumₜ t′
sumₜ-cong-≈ {zero} p = refl
sumₜ-cong-≈ {suc n} p = +-cong (p _) (sumₜ-cong-≈ (p ∘ suc))

-- '_≡_' is a congruence over 'sum n'.

sumₜ-cong-≡ : ∀ {n} {t t′ : Table Carrier n} → t ≗ t′ → sumₜ t ≡ sumₜ t′
sumₜ-cong-≡ {zero} p = P.refl
sumₜ-cong-≡ {suc n} p = P.cong₂ _+_ (p _) (sumₜ-cong-≡ (p ∘ suc))

-- The sum over the constantly zero function is zero.

sumₜ-zero : ∀ n → sumₜ (replicate {n} 0#) ≈ 0#
sumₜ-zero (zero) = refl
sumₜ-zero (suc n) =
  begin
    0# + sumₜ (replicate {n} 0#)  ≈⟨ proj₁ +-identity _ ⟩
    sumₜ (replicate {n} 0#)       ≈⟨ sumₜ-zero n ⟩
    0#                            ∎

-- The '∑' operator distributes over addition.

∑-distrib-+ : ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i + ∑[ i < n ] g i ≈ ∑[ i < n ] (f i + g i)
∑-distrib-+ zero f g = proj₁ +-identity _
∑-distrib-+ (suc n) f g =
  begin
    (fz + ∑f) + (gz + ∑g)      ≈⟨ solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ a ⊕ (c ⊕ (b ⊕ d))) refl fz ∑f gz ∑g ⟩
    fz + (gz + (∑f + ∑g))      ≈⟨ +-cong refl (+-cong refl (∑-distrib-+ n _ _)) ⟩
    fz + (gz + ∑fg)            ≈⟨ sym (+-assoc _ _ _) ⟩
    fz + gz + ∑fg              ∎
  where
  fz = f zero
  gz = g zero
  ∑f  = ∑[ i < n ] f (suc i)
  ∑g  = ∑[ i < n ] g (suc i)
  ∑fg = ∑[ i < n ] (f (suc i) + g (suc i))

-- The '∑' operator commutes with itself.

∑-comm : ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
∑-comm zero m f = sym (sumₜ-zero m)
∑-comm (suc n) m f =
  begin
    ∑[ j < m ] f zero j + ∑[ i < n ] ∑[ j < m ] f (suc i) j   ≈⟨ +-cong refl (∑-comm n m _) ⟩
    ∑[ j < m ] f zero j + ∑[ j < m ] ∑[ i < n ] f (suc i) j   ≈⟨ ∑-distrib-+ m _ _ ⟩
    ∑[ j < m ] (f zero j + ∑[ i < n ] f (suc i) j)            ∎

-- Any permutation of a table has the same sum as the original.

sumₜ-permute : ∀ {n} t (π : Permutation′ n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
sumₜ-permute {zero} t π = refl
sumₜ-permute {suc n} t π =
  begin
    sumₜ t                                                                      ≡⟨⟩
    f 0i + sumₜ (rearrange (punchIn 0i) t)                                      ≈⟨ +-cong refl (sumₜ-permute _ (Perm.remove (π ⟨$⟩ˡ 0i) π)) ⟩
    f 0i + sumₜ (rearrange (punchIn 0i ∘ (Perm.remove (π ⟨$⟩ˡ 0i) π ⟨$⟩ʳ_)) t)  ≡⟨ P.cong₂ _+_ P.refl (sumₜ-cong-≡ (P.cong f ∘ P.sym ∘ Perm.punchIn-permute′ π 0i)) ⟩
    f 0i + sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≡⟨ P.cong₂ _+_ (P.cong f (P.sym (Perm.inverseʳ π))) P.refl ⟩
    f _  + sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≈⟨ sym (sumₜ-punchIn (rearrange (π ⟨$⟩ʳ_) t) (π ⟨$⟩ˡ 0i)) ⟩
    sumₜ (rearrange (π ⟨$⟩ʳ_) t)                                                ∎
  where
  f = lookup t
  0i = zero
  ππ0 = π ⟨$⟩ʳ (π ⟨$⟩ˡ 0i)

-- A version of 'sumₜ-permute' allowing heterogeneous sum lengths.

sumₜ-permute′ : ∀ {m n} t (π : Permutation m n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
sumₜ-permute′ t π with Perm.↔⇒≡ π
sumₜ-permute′ t π | P.refl = sumₜ-permute t π

∑-permute : ∀ {n} f (π : Permutation′ n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (π ⟨$⟩ʳ i)
∑-permute = sumₜ-permute ∘ tabulate

∑-permute′ : ∀ {m n} f (π : Permutation m n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (π ⟨$⟩ʳ i)
∑-permute′ = sumₜ-permute′ ∘ tabulate

-- If the function takes the same value at 'i' and 'j', then transposing 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.

select-transpose : ∀ {n} t (i j : Fin n) → lookup t i ≈ lookup t j → ∀ k → (lookup (select 0# j t) ∘ PermC.transpose i j) k ≈ lookup (select 0# i t) k
select-transpose _ i j e k with k FP.≟ i
... | yes p rewrite P.≡-≟-identity FP._≟_ {j} P.refl = sym e
... | no ¬p with k FP.≟ j
... | yes q rewrite proj₂ (P.≢-≟-identity FP._≟_ (¬p ∘ P.trans q ∘ P.sym)) = refl
... | no ¬q rewrite proj₂ (P.≢-≟-identity FP._≟_ ¬q) = refl

-- Summing over a pulse gives you the single value picked out by the pulse.

sumₜ-select : ∀ {n i} (t : Table Carrier n) → sumₜ (select 0# i t) ≈ lookup t i
sumₜ-select {zero} {()} t
sumₜ-select {suc n} {i} t =
  begin
    sumₜ (select 0# i t)                                                        ≈⟨ sumₜ-permute (select 0# i t) (Perm.transpose zero i) ⟩
    sumₜ (rearrange (PermC.transpose zero i) (select 0# i t))                   ≡⟨ sumₜ-cong-≡ (TP.select-const 0# i t ∘ PermC.transpose zero i) ⟩
    sumₜ (rearrange (PermC.transpose zero i) (select 0# i (replicate (f i))))   ≈⟨ sumₜ-cong-≈ (select-transpose (replicate (f i)) zero i refl) ⟩
    sumₜ (select 0# zero (replicate {suc n} (f i)))                             ≡⟨⟩
    f i + sumₜ (replicate {n} 0#)                                               ≈⟨ +-cong refl (sumₜ-zero n) ⟩
    f i + 0#                                                                    ≈⟨ proj₂ +-identity _ ⟩
    f i                                                                         ∎
  where
  f = lookup t

-- Converting to a table then summing is the same as summing the original list

sumₜ-fromList : ∀ xs → sumₜ (fromList xs) ≡ sumₗ xs
sumₜ-fromList [] = P.refl
sumₜ-fromList (x ∷ xs) = P.cong₂ _+_ P.refl (sumₜ-fromList xs)

-- Converting to a list then summing is the same as summing the original table

sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (toList t)
sumₜ-toList {zero} _ = P.refl
sumₜ-toList {suc n} _ = P.cong₂ _+_ P.refl (sumₜ-toList {n} _)

-- If addition is idempotent on a particular value 'x', then summing over any
-- arbitrary number of copies of 'x' gives back 'x'.

sumₜ-idem-replicate : ∀ n {x} → _+_ IdempotentOn x → sumₜ (Table.replicate {suc n} x) ≈ x
sumₜ-idem-replicate zero idem = proj₂ +-identity _
sumₜ-idem-replicate (suc n) {x} idem = begin
  x + (x + sumₜ (Table.replicate {n} x))   ≈⟨ sym (+-assoc _ _ _) ⟩
  (x + x) + sumₜ (Table.replicate {n} x)   ≈⟨ +-cong idem refl ⟩
  x + sumₜ (Table.replicate {n} x)         ≈⟨ sumₜ-idem-replicate n idem ⟩
  x ∎

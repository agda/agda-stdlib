------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.CommutativeMonoid {g₁ g₂} (M : CommutativeMonoid g₁ g₂) where

open import Algebra.Operations.CommutativeMonoid M
open import Algebra.Solver.CommutativeMonoid M
open import Relation.Binary as B using (_Preserves_⟶_)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using ([]; _∷_)
import Data.Fin.Properties as FP
open import Data.Fin.Permutation as Perm using (Permutation; Permutation′; _⟨$⟩ˡ_; _⟨$⟩ʳ_)
open import Data.Fin.Permutation.Components as PermC
open import Data.Table as Table
open import Data.Table.Relation.Binary.Equality as TE using (_≗_)
open import Data.Unit using (tt)
import Data.Table.Properties as TP
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open CommutativeMonoid M
  renaming
  ( ε         to 0#
  ; _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congˡ   to +-congˡ
  ; ∙-congʳ   to +-congʳ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; comm      to +-comm
  )
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.Reasoning.Setoid setoid

module _ {n} where
  open B.Setoid (TE.setoid setoid n) public
    using ()
    renaming (_≈_ to _≋_)

-- When summing over a function from a finite set, we can pull out any value and move it to the front.

sumₜ-remove : ∀ {n} {i : Fin (suc n)} t → sumₜ t ≈ lookup t i + sumₜ (remove i t)
sumₜ-remove {_}     {zero}   t = refl
sumₜ-remove {zero}  {suc ()} t
sumₜ-remove {suc n} {suc i}  t′ =
  begin
    t₀ + ∑t           ≈⟨ +-congʳ (sumₜ-remove t) ⟩
    t₀ + (tᵢ + ∑t′)   ≈⟨ solve 3 (λ x y z → x ⊕ (y ⊕ z) ⊜ y ⊕ (x ⊕ z)) refl t₀ tᵢ ∑t′ ⟩
    tᵢ + (t₀ + ∑t′)   ∎
  where
  t = tail t′
  t₀ = head t′
  tᵢ = lookup t i
  ∑t = sumₜ t
  ∑t′ = sumₜ (remove i t)

-- '_≈_' is a congruence over 'sumTable n'.

sumₜ-cong-≈ : ∀ {n} → sumₜ {n} Preserves _≋_ ⟶ _≈_
sumₜ-cong-≈ {zero}  p = refl
sumₜ-cong-≈ {suc n} p = +-cong (p _) (sumₜ-cong-≈ (p ∘ suc))

-- '_≡_' is a congruence over 'sum n'.

sumₜ-cong-≡ : ∀ {n} → sumₜ {n} Preserves _≗_ ⟶ _≡_
sumₜ-cong-≡ {zero}  p = P.refl
sumₜ-cong-≡ {suc n} p = P.cong₂ _+_ (p _) (sumₜ-cong-≡ (p ∘ suc))

-- If addition is idempotent on a particular value 'x', then summing over a
-- nonzero number of copies of 'x' gives back 'x'.

sumₜ-idem-replicate : ∀ n {x} → _+_ IdempotentOn x → sumₜ (replicate {n = suc n} x) ≈ x
sumₜ-idem-replicate zero        idem = +-identityʳ _
sumₜ-idem-replicate (suc n) {x} idem = begin
  x + (x + sumₜ (replicate {n = n} x))  ≈⟨ sym (+-assoc _ _ _) ⟩
  (x + x) + sumₜ (replicate {n = n} x)  ≈⟨ +-congˡ idem ⟩
  x + sumₜ (replicate {n = n} x)        ≈⟨ sumₜ-idem-replicate n idem ⟩
  x                                 ∎

-- The sum over the constantly zero function is zero.

sumₜ-zero : ∀ n → sumₜ (replicate {n = n} 0#) ≈ 0#
sumₜ-zero n = begin
  sumₜ (replicate {n = n} 0#)      ≈⟨ sym (+-identityˡ _) ⟩
  0# + sumₜ (replicate {n = n} 0#) ≈⟨ sumₜ-idem-replicate n (+-identityˡ 0#) ⟩
  0#                               ∎

-- The '∑' operator distributes over addition.

∑-distrib-+ : ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] (f i + g i) ≈ ∑[ i < n ] f i + ∑[ i < n ] g i
∑-distrib-+ zero    f g = sym (+-identityˡ _)
∑-distrib-+ (suc n) f g = begin
  f₀ + g₀ + ∑fg          ≈⟨ +-assoc _ _ _ ⟩
  f₀ + (g₀ + ∑fg)        ≈⟨ +-congʳ (+-congʳ (∑-distrib-+ n _ _)) ⟩
  f₀ + (g₀ + (∑f + ∑g))  ≈⟨ solve 4 (λ a b c d → a ⊕ (c ⊕ (b ⊕ d)) ⊜ (a ⊕ b) ⊕ (c ⊕ d)) refl f₀ ∑f g₀ ∑g ⟩
  (f₀ + ∑f) + (g₀ + ∑g)  ∎
  where
  f₀ = f zero
  g₀ = g zero
  ∑f  = ∑[ i < n ] f (suc i)
  ∑g  = ∑[ i < n ] g (suc i)
  ∑fg = ∑[ i < n ] (f (suc i) + g (suc i))

-- The '∑' operator commutes with itself.

∑-comm : ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
∑-comm zero    m f = sym (sumₜ-zero m)
∑-comm (suc n) m f = begin
  ∑[ j < m ] f zero j + ∑[ i < n ] ∑[ j < m ] f (suc i) j  ≈⟨ +-congʳ (∑-comm n m _) ⟩
  ∑[ j < m ] f zero j + ∑[ j < m ] ∑[ i < n ] f (suc i) j  ≈⟨ sym (∑-distrib-+ m _ _) ⟩
  ∑[ j < m ] (f zero j + ∑[ i < n ] f (suc i) j)           ∎

-- Any permutation of a table has the same sum as the original.

sumₜ-permute : ∀ {m n} t (π : Permutation m n) → sumₜ t ≈ sumₜ (permute π t)
sumₜ-permute {zero}  {zero}  t π = refl
sumₜ-permute {zero}  {suc n} t π = contradiction π (Perm.refute λ())
sumₜ-permute {suc m} {zero}  t π = contradiction π (Perm.refute λ())
sumₜ-permute {suc m} {suc n} t π = begin
  sumₜ t                                                                            ≡⟨⟩
  lookup t 0i           + sumₜ (remove 0i t)                                        ≡⟨ P.cong₂ _+_ (P.cong (lookup t) (P.sym (Perm.inverseʳ π))) P.refl ⟩
  lookup πt (π ⟨$⟩ˡ 0i) + sumₜ (remove 0i t)                                        ≈⟨ +-congʳ (sumₜ-permute (remove 0i t) (Perm.remove (π ⟨$⟩ˡ 0i) π)) ⟩
  lookup πt (π ⟨$⟩ˡ 0i) + sumₜ (permute (Perm.remove (π ⟨$⟩ˡ 0i) π) (remove 0i t))  ≡⟨ P.cong₂ _+_ P.refl (sumₜ-cong-≡ (P.sym ∘ TP.remove-permute π 0i t)) ⟩
  lookup πt (π ⟨$⟩ˡ 0i) + sumₜ (remove (π ⟨$⟩ˡ 0i) πt)                              ≈⟨ sym (sumₜ-remove (permute π t)) ⟩
  sumₜ πt                                                                           ∎
  where
  0i = zero
  πt = permute π t

∑-permute : ∀ {m n} f (π : Permutation m n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (π ⟨$⟩ʳ i)
∑-permute = sumₜ-permute ∘ tabulate

-- If the function takes the same value at 'i' and 'j', then transposing 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.

select-transpose : ∀ {n} t (i j : Fin n) → lookup t i ≈ lookup t j → ∀ k → (lookup (select 0# j t) ∘ PermC.transpose i j) k ≈ lookup (select 0# i t) k
select-transpose _ i j e k with k FP.≟ i
... | yes p rewrite P.≡-≟-identity FP._≟_ {j} P.refl = sym e
... | no ¬p with k FP.≟ j
...   | no ¬q rewrite proj₂ (P.≢-≟-identity FP._≟_ ¬q) = refl
...   | yes q rewrite proj₂ (P.≢-≟-identity FP._≟_
                               (¬p ∘ P.trans q ∘ P.sym)) = refl

-- Summing over a pulse gives you the single value picked out by the pulse.

sumₜ-select : ∀ {n i} (t : Table Carrier n) → sumₜ (select 0# i t) ≈ lookup t i
sumₜ-select {zero}  {()}
sumₜ-select {suc n} {i} t = begin
  sumₜ (select 0# i t)                                        ≈⟨ sumₜ-remove {i = i} (select 0# i t) ⟩
  lookup (select 0# i t) i + sumₜ (remove i (select 0# i t))  ≡⟨ P.cong₂ _+_ (TP.select-lookup t) (sumₜ-cong-≡ (TP.select-remove i t)) ⟩
  lookup t i + sumₜ (replicate {n = n} 0#)                    ≈⟨ +-congʳ (sumₜ-zero n) ⟩
  lookup t i + 0#                                             ≈⟨ +-identityʳ _ ⟩
  lookup t i                                                  ∎

-- Converting to a table then summing is the same as summing the original list

sumₜ-fromList : ∀ xs → sumₜ (fromList xs) ≡ sumₗ xs
sumₜ-fromList []       = P.refl
sumₜ-fromList (x ∷ xs) = P.cong (_ +_) (sumₜ-fromList xs)

-- Converting to a list then summing is the same as summing the original table

sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (toList t)
sumₜ-toList {zero}  _ = P.refl
sumₜ-toList {suc n} _ = P.cong (_ +_) (sumₜ-toList {n} _)

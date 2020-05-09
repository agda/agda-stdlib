------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Vec.Functional` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from other Table modules
{-# OPTIONS --warn=noUserWarning #-}

module Data.Table.Properties where

{-# WARNING_ON_IMPORT
"Data.Table.Properties was deprecated in v1.2.
Use Data.Vec.Functional.Properties instead."
#-}

open import Data.Table
open import Data.Table.Relation.Binary.Equality

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Nat.Base using (zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; suc; zero; _≟_; punchIn)
import Data.Fin.Properties as FP
open import Data.Fin.Permutation as Perm using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open import Data.List.Base as L using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Vec.Base as V using (Vec; _∷_; [])
import Data.Vec.Properties as VP
open import Level using (Level)
open import Function.Base using (_∘_; flip)
open import Function.Inverse using (Inverse)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- select

-- Selecting from any table is the same as selecting from a constant table.

select-const : ∀ {n} (z : A) (i : Fin n) t →
               select z i t ≗ select z i (replicate (lookup t i))
select-const z i t j with does (j ≟ i)
... | true  = refl
... | false = refl

-- Selecting an element from a table then looking it up is the same as looking
-- up the index in the original table

select-lookup : ∀ {n x i} (t : Table A n) →
                lookup (select x i t) i ≡ lookup t i
select-lookup {i = i} t rewrite dec-true (i ≟ i) refl = refl

-- Selecting an element from a table then removing the same element produces a
-- constant table

select-remove : ∀ {n x} i (t : Table A (suc n)) →
                remove i (select x i t) ≗ replicate {n = n} x
select-remove i t j rewrite dec-false (punchIn i j ≟ i) (FP.punchInᵢ≢i _ _)
                          = refl


------------------------------------------------------------------------
-- permute

-- Removing an index 'i' from a table permuted with 'π' is the same as
-- removing the element, then permuting with 'π' minus 'i'.

remove-permute : ∀ {m n} (π : Permutation (suc m) (suc n))
                 i (t : Table A (suc n)) →
                 remove (π ⟨$⟩ˡ i) (permute π t)
                 ≗ permute (Perm.remove (π ⟨$⟩ˡ i) π) (remove i t)
remove-permute π i t j = P.cong (lookup t) (Perm.punchIn-permute′ π i j)

------------------------------------------------------------------------
-- fromList

fromList-∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → lookup (fromList xs) i ∈ xs
fromList-∈ {xs = x ∷ xs} zero    = here refl
fromList-∈ {xs = x ∷ xs} (suc i) = there (fromList-∈ i)

index-fromList-∈ : ∀ {xs : List A} {i} → index (fromList-∈ {xs = xs} i) ≡ i
index-fromList-∈ {xs = x ∷ xs} {zero}  = refl
index-fromList-∈ {xs = x ∷ xs} {suc i} = cong suc index-fromList-∈

fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) → lookup (fromList xs) (index x∈xs) ≡ x
fromList-index (here px)    = sym px
fromList-index (there x∈xs) = fromList-index x∈xs

------------------------------------------------------------------------
-- There exists an isomorphism between tables and vectors.

↔Vec : ∀ {n} → Inverse (≡-setoid A n) (P.setoid (Vec A n))
↔Vec = record
  { to = record { _⟨$⟩_ = toVec ; cong = VP.tabulate-cong }
  ; from = P.→-to-⟶ fromVec
  ; inverse-of = record
    { left-inverse-of  = VP.lookup∘tabulate ∘ lookup
    ; right-inverse-of = VP.tabulate∘lookup
    }
  }

------------------------------------------------------------------------
-- Other

lookup∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → ∃ λ x → x ∈ xs
lookup∈ i = _ , fromList-∈ i

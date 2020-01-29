------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on vectors, presented as functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Properties where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (Fin; zero; suc; _≟_; punchIn)
open import Data.Fin.Permutation as Perm using (Permutation; _⟨$⟩ˡ_)
import Data.Fin.Properties as Fₚ
open import Data.List.Base as List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (∃; _,_)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Binary.Pointwise.Extensional as VecPw
open import Data.Vec.Functional
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pw
open import Function.Inverse using (Inverse)
open import Level using (Level)
open import Relation.Binary using (Setoid)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; refl; cong; sym; setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (dec-true; dec-false)

private
  variable
    a c r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- select

-- Selecting from any table is the same as selecting from a constant table.

select-const : ∀ {n} (z : A) (i : Fin n) t →
               select z i t ≗ select z i (replicate (t i))
select-const z i t j with does (j ≟ i)
... | true  = refl
... | false = refl

-- Selecting an element from a table then looking it up is the same as looking
-- up the index in the original table

select-lookup : ∀ {n x i} (t : Vector A n) →
                select x i t i ≡ t i
select-lookup {i = i} t rewrite dec-true (i ≟ i) refl = refl

-- Selecting an element from a table then removing the same element produces a
-- constant table

select-remove : ∀ {n x} i (t : Vector A (suc n)) →
                remove i (select x i t) ≗ replicate {n = n} x
select-remove i t j rewrite dec-false (punchIn i j ≟ i) (Fₚ.punchInᵢ≢i _ _)
                          = refl

------------------------------------------------------------------------
-- permute

-- Removing an index 'i' from a table permuted with 'π' is the same as
-- removing the element, then permuting with 'π' minus 'i'.

remove-permute : ∀ {m n} (π : Permutation (suc m) (suc n))
                 i (t : Vector A (suc n)) →
                 remove (π ⟨$⟩ˡ i) (permute π t)
                 ≗ permute (Perm.remove (π ⟨$⟩ˡ i) π) (remove i t)
remove-permute π i t j = P.cong t (Perm.punchIn-permute′ π i j)

------------------------------------------------------------------------
-- fromList

fromList-∈ : ∀ {xs : List A} (i : Fin (List.length xs)) → fromList xs i ∈ xs
fromList-∈ {xs = x ∷ xs} zero    = here refl
fromList-∈ {xs = x ∷ xs} (suc i) = there (fromList-∈ i)

index-fromList-∈ : ∀ {xs : List A} {i} → index (fromList-∈ {xs = xs} i) ≡ i
index-fromList-∈ {xs = x ∷ xs} {zero}  = refl
index-fromList-∈ {xs = x ∷ xs} {suc i} = cong suc index-fromList-∈

fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) →
                 fromList xs (index x∈xs) ≡ x
fromList-index (here px)    = sym px
fromList-index (there x∈xs) = fromList-index x∈xs

------------------------------------------------------------------------
-- There exists an isomorphism between vectors as functions on the one
-- and and vectors as datatypes on the other.

module _ (S@record { Carrier = A } : Setoid c ℓ) where

  ↔Vec : ∀ {n} → Inverse (Pw.setoid S n) (VecPw.setoid S n)
  ↔Vec = record
    { to         = record
      { _⟨$⟩_ = Vec.tabulate
      ; cong  = λ {xs} {ys} R → VecPw.ext λ i → let open Reasoning S in begin
        Vec.lookup (Vec.tabulate xs) i ≡⟨ Vecₚ.lookup∘tabulate xs i ⟩
        xs i                           ≈⟨ R i ⟩
        ys i                           ≡˘⟨ Vecₚ.lookup∘tabulate ys i ⟩
        Vec.lookup (Vec.tabulate ys) i ∎
      }
    ; from       = record
      { _⟨$⟩_ = Vec.lookup
      ; cong  = VecPw.Pointwise.app
      }
    ; inverse-of = record
      { left-inverse-of  = λ f i → reflexive S (Vecₚ.lookup∘tabulate f i)
      ; right-inverse-of = λ xs  → reflexive (VecPw.setoid S _) (Vecₚ.tabulate∘lookup xs)
      }
    } where open Setoid

------------------------------------------------------------------------
-- Other

lookup∈ : ∀ {xs : List A} (i : Fin (List.length xs)) → ∃ λ x → x ∈ xs
lookup∈ i = _ , fromList-∈ i

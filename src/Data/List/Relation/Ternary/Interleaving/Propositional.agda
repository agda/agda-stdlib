------------------------------------------------------------------------
-- The Agda standard library
--
-- Interleavings of lists using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Ternary.Interleaving.Propositional {a} {A : Set a} where

open import Level using (_⊔_)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise as Pw using ()
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Permutation.Propositional as Perm using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (shift)
import Data.List.Relation.Ternary.Interleaving.Setoid as General
open import Relation.Binary.PropositionalEquality using (setoid; refl)
open Perm.PermutationReasoning

------------------------------------------------------------------------
-- Re-export the basic combinators

open General hiding (Interleaving) public

------------------------------------------------------------------------
-- Definition

Interleaving : List A → List A → List A → Set a
Interleaving = General.Interleaving (setoid A)

pattern consˡ xs = refl ∷ˡ xs
pattern consʳ xs = refl ∷ʳ xs

------------------------------------------------------------------------
-- New combinators

toPermutation : ∀ {l r as} → Interleaving l r as → as ↭ l ++ r
toPermutation []         = Perm.refl
toPermutation (consˡ sp) = Perm.prep _ (toPermutation sp)
toPermutation {l} {r ∷ rs} {a ∷ as} (consʳ sp) = begin
  a ∷ as       ↭⟨ Perm.prep a (toPermutation sp) ⟩
  a ∷ l ++ rs  ↭⟨ Perm.↭-sym (shift a l rs) ⟩
  l ++ a ∷ rs  ∎

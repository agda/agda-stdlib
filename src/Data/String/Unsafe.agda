------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe String operations and proofs
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.String.Unsafe where

import Data.List.Base as List
import Data.List.Properties as Listₚ
open import Data.Nat.Base using (_+_)
open import Data.String.Base

open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

------------------------------------------------------------------------
-- Properties of conversion functions

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe

toList-++ : ∀ s t → toList (s ++ t) ≡ toList s List.++ toList t
toList-++ s t = trustMe

length-++ : ∀ s t → length (s ++ t) ≡ length s + length t
length-++ s t = begin
  length (s ++ t)                         ≡⟨⟩
  List.length (toList (s ++ t))           ≡⟨ cong List.length (toList-++ s t) ⟩
  List.length (toList s List.++ toList t) ≡⟨ Listₚ.length-++ (toList s) ⟩
  length s + length t                     ∎

length-replicate : ∀ n {c} → length (replicate n c) ≡ n
length-replicate n {c} = let cs = List.replicate n c in begin
  length (replicate n c) ≡⟨ cong List.length (toList∘fromList cs) ⟩
  List.length cs         ≡⟨ Listₚ.length-replicate n ⟩
  n                      ∎

------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.Properties where

open import Level using (Level)
open import Data.List.Base
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.Queue.Base using (toList; fromList; empty; mkQ)
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

toList-fromList : {xs : List A}  → toList (fromList xs) ≡ xs
toList-fromList {a} {A} {[]} =
  begin
    toList (fromList [])
  ≡⟨⟩
    toList (empty)
  ≡⟨⟩
    []
  ∎

toList-fromList {a} {A} {x ∷ xs} =
  begin
    toList (fromList (x ∷ xs))
  ≡⟨⟩
    toList (mkQ (x ∷ xs) [] (λ _ → []))
  ≡⟨⟩
    (x ∷ xs) ++ (reverse [])
  ≡⟨⟩
    (x ∷ xs) ++ []
  ≡⟨ ++-identityʳ (x ∷ xs) ⟩
    (x ∷ xs)
  ∎

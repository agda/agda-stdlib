------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Properties where

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List.Base
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Queue.TwoList.Base
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary using (¬_)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

  ¬Null : {a : A} {as : List A} → ¬ (Null (a ∷ as))
  ¬Null (() Data.List.Relation.Unary.All.∷ n)

toList-fromList : (xs : List A)  → toList (fromList xs) ≡ xs
toList-fromList [] = begin
  toList (fromList []) ≡⟨⟩
  toList (empty)       ≡⟨⟩
  []                   ∎

toList-fromList (x ∷ xs) = begin
  toList (fromList (x ∷ xs))          ≡⟨⟩
  toList (mkQ (x ∷ xs) [] (λ _ → [])) ≡⟨⟩
  (x ∷ xs) ++ (reverse [])            ≡⟨⟩
  (x ∷ xs) ++ []                      ≡⟨ ++-identityʳ (x ∷ xs) ⟩
  (x ∷ xs)                            ∎

-- enqueue increases size by 1
enqueueSuc : (a : A) (q : Queue A) → (size (enqueue a q)) ≡ (suc (size q))
enqueueSuc a (mkQ [] back inv) = refl
enqueueSuc a (mkQ (x ∷ front) back inv) = begin
  size (enqueue a (mkQ (x ∷ front) back inv))                ≡⟨⟩
  size (mkQ (x ∷ front) (a ∷ back) (λ n → ⊥-elim (¬Null n))) ≡⟨⟩
  length (x ∷ front) + length (a ∷ back)                     ≡⟨⟩
  length (x ∷ front) + suc (length back) ≡⟨ +-suc (length (x ∷ front)) (length back) ⟩
  suc (length (x ∷ front) + length back)                     ∎

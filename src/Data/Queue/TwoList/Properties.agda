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

toList-fromList xs@(_ ∷ _) = begin
  toList (fromList xs)          ≡⟨⟩
  toList (mkQ xs [] (λ _ → [])) ≡⟨⟩
  xs ++ (reverse [])            ≡⟨⟩
  xs ++ []                      ≡⟨ ++-identityʳ xs ⟩
  xs                            ∎

-- enqueue increases size by 1
-- feels uneccesarily complex for the empty front case?
-- rewrite could make it cleaner, but are we trying to use that less?
size-enqueue : (x : A) (q : Queue A) → (size (enqueue x q)) ≡ (suc (size q))
size-enqueue {A = A} x q@(mkQ [] back inv) = begin
  size (enqueue x (mkQ [] back inv)) ≡⟨⟩
  size (queue (x ∷ []) [])           ≡⟨⟩
  suc 0                              ≡⟨ cong suc (sym sizeq) ⟩
  suc (size q)                       ∎
  where
    null[] : Null back → back ≡ []
    null[] [] = refl

    back[] : back ≡ []
    back[] = null[] (inv [])

    sizeq : size q ≡ 0
    sizeq = begin
      size q                          ≡⟨⟩
      length {A = A} [] + length back ≡⟨⟩
      0 + length back                 ≡⟨⟩
      length back                     ≡⟨ cong length back[] ⟩
      length {A = A} []               ≡⟨⟩
      0                               ∎

size-enqueue a (mkQ (x ∷ front) back inv) = begin
  size (enqueue a (mkQ (x ∷ front) back inv))                ≡⟨⟩
  size (mkQ (x ∷ front) (a ∷ back) (λ n → ⊥-elim (¬Null n))) ≡⟨⟩
  length (x ∷ front) + length (a ∷ back)                     ≡⟨⟩
  length (x ∷ front) + suc (length back) ≡⟨ +-suc (length (x ∷ front)) (length back) ⟩
  suc (length (x ∷ front) + length back) ∎

-- trivial, but ensures empty works correctly
size-empty : size (empty {a} {A}) ≡ 0
size-empty = refl


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
open import Data.List.Properties using (++-identityʳ; length-++; length-reverse)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Data.Queue.TwoList.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (¬_)

open ≡-Reasoning
open RawQueue {{...}} using (size)

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
-- rewrite could make it cleaner, but are we trying to use that less?
size-enqueue : (x : A) (q : Queue A) → (size (enqueue {a} x q)) ≡ (suc (size q))
size-enqueue {a = a} {A = A} x q@(mkQ [] back inv) = begin
  size (queue (x ∷ []) []) ≡⟨⟩
  length (x ∷ []) ≡⟨⟩
  suc 0 ≡⟨ cong suc (sym sizeq) ⟩
  suc (size q) ∎
  where
    null[] : Null back → back ≡ []
    null[] [] = refl

    back[] : back ≡ []
    back[] = null[] (inv [])

    -- why does length need {a} and {A} after reverse back ↦ reverse []?
    sizeq : size q ≡ 0
    sizeq = begin
      size q                         ≡⟨⟩
      length (toList q)              ≡⟨⟩
      length ([] ++ (reverse back))  ≡⟨⟩
      length (reverse back)          ≡⟨ cong (length ∘ reverse) back[] ⟩
      length {a} {A} (reverse [])    ≡⟨⟩
      length {a} {A} []              ≡⟨⟩
      0                              ∎

size-enqueue {A = A} x q@(mkQ front@(_ ∷ _) back inv) = begin
  size (queue front (x ∷ back)) ≡⟨⟩
  length (front ++ (reverse ( x ∷ back)))    ≡⟨ length-++ front ⟩
  length front + length (reverse (x ∷ back)) ≡⟨ cong (_+_ (length front)) (length-reverse (x ∷ back)) ⟩
  length front + length (x ∷ back)           ≡⟨⟩
  length front + suc (length back)           ≡⟨ cong ((_+_ (length front)) ∘ suc) (sym (length-reverse back)) ⟩
  length front + suc (length (reverse back)) ≡⟨ +-suc (length front) (length (reverse back)) ⟩
  suc (length front + length (reverse back)) ≡⟨ cong suc (sym (length-++ front {reverse (back)})) ⟩
  suc (length (front ++ (reverse back)))     ≡⟨⟩
  suc (length (toList q))                    ≡⟨⟩
  suc (size q)                               ∎

-- trivial, but ensures empty works correctly
size-empty : size (empty {a} {A}) ≡ 0
size-empty = refl

------------------------------------------------------------------------
-- Properties of _≈_

-- it becomes propositional equality on lists, so easy!
≈-isEquivalence : IsEquivalence (_≈_ {A = A})
≈-isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

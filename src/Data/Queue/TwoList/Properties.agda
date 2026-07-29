------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue-related properties
------------------------------------------------------------------------

-- {-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Properties where

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List.Base
open import Data.List.Properties using (++-identityʳ; length-++; length-reverse)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-assoc)
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Data.Queue.TwoList.Base
open import Data.SnocList.Base as SnocList using (List<; []; _<:_; toList>; fromList>)
open import Data.SnocList.Properties using (toList>-fromList>)
open import Data.SnocList.Relation.Unary.All using (All<; Null<; []; _<:_)
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

  ¬Null : {x : A} {xs : List A} → ¬ Null (x ∷ xs)
  ¬Null (() Data.List.Relation.Unary.All.∷ n)

  null-<: : ∀ {x} {xs : List< A} {ys : List A} → Null< (xs <: x) → Null ys
  null-<: (()<: _)

  queue-back[] : ∀ {xs : List< A} → (Queue.back (queue xs [])) ≡ []
  queue-back[] {xs = []} = refl
  queue-back[] {xs = xs <: x} = refl

  queue-front : ∀ {xs : List< A} → (Queue.front (queue xs [])) ≡ xs
  queue-front {xs = []} = refl
  queue-front {xs = xs <: x} = refl
  
toList-fromList : ∀ {q : Queue A} {xs : List A} → q ≈ fromList xs → toList q ≡ xs
toList-fromList {q = q} {xs = xs} q≈xs = begin
  toList q             ≡⟨ q≈xs ⟩
  toList (fromList xs) ≡⟨ toList-fromList' {xs = xs} ⟩
  xs                   ∎
  where
    toList-fromList' : ∀ {xs : List A} → toList (fromList xs) ≡ xs
    toList-fromList' {xs = xs} = begin
      toList (fromList xs)             ≡⟨⟩
      toList (queue (fromList> xs) []) ≡⟨⟩
      (Queue.back (queue (fromList> xs) [])) ++ (toList> (Queue.front (queue (fromList> xs) []))) ≡⟨ cong₂ _++_ (queue-back[] {xs = fromList> xs}) refl ⟩
      [] ++ (toList> (Queue.front (queue (fromList> xs) [])))  ≡⟨⟩
      (toList> (Queue.front (queue (fromList> xs) []))) ≡⟨ cong toList> (queue-front {xs = fromList> xs}) ⟩
      toList> (fromList> xs) ≡⟨ toList>-fromList> xs ⟩
      xs ∎

-- enqueue increases size by 1
-- rewrite could make it cleaner, but are we trying to use that less?
size-enqueue : (x : A) (q : Queue A) → (size (enqueue {a} x q)) ≡ (suc (size q))
size-enqueue {a = a} {A = A} x q@(mkQ [] back inv) = begin
  size (queue ([] <: x) []) ≡⟨⟩
  length (x ∷ [])           ≡⟨⟩
  suc 0                     ≡⟨ cong suc (sym sizeq) ⟩
  suc (size q)              ∎
  where
    null[] : Null back → back ≡ []
    null[] [] = refl

    back[] : back ≡ []
    back[] = null[] (inv [])

    -- why does length need {a} and {A} after back ↦ []?
    sizeq : size q ≡ 0
    sizeq = begin
      size q              ≡⟨⟩
      length (toList q)   ≡⟨⟩
      length (back ++ []) ≡⟨ cong length (++-identityʳ back) ⟩
      length (back)       ≡⟨ cong length back[] ⟩
      length {a} {A} []   ≡⟨⟩
      0 ∎    

size-enqueue {A = A} x q@(mkQ front@(_ <: _) back inv) = begin
  size (queue front (x ∷ back))              ≡⟨⟩
  length ((x ∷ back) ++ (toList> front))     ≡⟨ length-++ (x ∷ back) ⟩
  length (x ∷ back) + length (toList> front) ≡⟨⟩
  suc (length back) + length (toList> front) ≡⟨ +-comm (suc (length back)) (length (toList> front)) ⟩
  length (toList> front) + suc (length back) ≡⟨ +-suc (length (toList> front)) (length back)⟩
  suc (length (toList> front) + length back) ≡⟨ cong suc (+-comm (length (toList> front)) (length back)) ⟩
  suc (length back + length (toList> front)) ≡⟨ cong suc (sym (length-++ back {toList> front})) ⟩
  suc (length (back ++ (toList> front)))     ≡⟨⟩
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

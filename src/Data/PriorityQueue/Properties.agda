------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of priority queue
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (TotalOrder)
open import Data.PriorityQueue.Base

module Data.PriorityQueue.Properties
  {a ℓ₁ ℓ₂} {b ℓ}
  (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  (priorityQueue : PriorityQueue totalOrder b ℓ)
  where

open import Data.Empty
import Data.Empty.Irrelevant as Irrelevant
open import Data.List
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Induction.WellFounded

open TotalOrder totalOrder renaming (Carrier to A)
open PriorityQueue priorityQueue

popMin⇒deleteMin : ∀ {q t} → popMin q ≡ t → deleteMin q ≡ Maybe.map proj₂ t
popMin⇒deleteMin = P.cong (Maybe.map proj₂)

popMin′ : ∀ q → .(¬Empty q) → A × Queue
popMin′ q q≢∅ with popMin q
... | nothing = Irrelevant.⊥-elim (q≢∅ P.refl)
... | just p = p

findMin′ : ∀ q → .(¬Empty q) → A
findMin′ q q≢∅ = proj₁ (popMin′ q q≢∅)

deleteMin′ : ∀ q → .(¬Empty q) → Queue
deleteMin′ q q≢∅ = proj₂ (popMin′ q q≢∅)

Empty-empty : Empty empty
Empty-empty = size≡0⇒Empty empty size-empty

toListAux-irrelevant : ∀ q (rec₁ rec₂ : Acc _≺_ q) → toListAux q rec₁ ≡ toListAux q rec₂
toListAux-irrelevant q (acc rs₁) (acc rs₂) with popMin q
... | nothing = P.refl
... | just (x , q') = P.cong (x ∷_) (toListAux-irrelevant q' (rs₁ q' P.refl) (rs₂ q' P.refl))

toListAux-length : ∀ q (@0 rec : Acc _≺_ q) → length (toListAux q rec) ≡ size q
toListAux-length q (acc rs) with popMin q in eq
... | nothing = P.sym (Empty⇒size≡0 q eq)
... | just (x , q') = begin
  1 + length (toListAux q' (rs q' P.refl)) ≡⟨ P.cong suc (toListAux-length q' (rs q' P.refl)) ⟩
  1 + size q'                              ≡˘⟨ ≺-size q q' (popMin⇒deleteMin eq) ⟩
  size q                                   ∎
  where open P.≡-Reasoning

toList-length : ∀ q → length (toList q) ≡ size q
toList-length q = toListAux-length q (≺-wellFounded q)

toListAux-Empty : ∀ q (@0 rec : Acc _≺_ q) → Empty q → toListAux q rec ≡ []
toListAux-Empty q (acc rs) q≡∅ with popMin q
toListAux-Empty q (acc rs) refl   | nothing = P.refl

toList-Empty : ∀ q → Empty q → toList q ≡ []
toList-Empty q = toListAux-Empty q (≺-wellFounded q)

toList-empty : toList empty ≡ []
toList-empty = toList-Empty empty (Empty-empty)

toList-unfold : ∀ q x q' → PopMin q x q' → toList q ≡ x ∷ toList q'
toList-unfold q x q' p    with ≺-wellFounded q
toList-unfold q x q' p    | acc rs with popMin q in eq
toList-unfold q x q' refl | acc rs | just (x , q') =
  P.cong (x ∷_) (toListAux-irrelevant q' rec₁ rec₂)
  where
    rec₁ = rs q' P.refl
    rec₂ = ≺-wellFounded q'

------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets, based on AVL trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Sets
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ)
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.Unit.Base
open import Function.Base
open import Level using (Level; _⊔_)

private
  variable
    b : Level
    B : Set b

import Data.Tree.AVL.Map strictTotalOrder as AVL
open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

------------------------------------------------------------------------
-- The set type (note that Set is a reserved word)

⟨Set⟩ : Set (a ⊔ ℓ₂)
⟨Set⟩ = AVL.Map ⊤

------------------------------------------------------------------------
-- Repackaged functions

empty : ⟨Set⟩
empty = AVL.empty

singleton : A → ⟨Set⟩
singleton k = AVL.singleton k _

insert : A → ⟨Set⟩ → ⟨Set⟩
insert k = AVL.insert k _

delete : A → ⟨Set⟩ → ⟨Set⟩
delete = AVL.delete

infix 4 _∈?_

_∈?_ : A → ⟨Set⟩ → Bool
_∈?_ = AVL._∈?_

headTail : ⟨Set⟩ → Maybe (A × ⟨Set⟩)
headTail s = Maybe.map (Prod.map₁ proj₁) (AVL.headTail s)

initLast : ⟨Set⟩ → Maybe (⟨Set⟩ × A)
initLast s = Maybe.map (Prod.map₂ proj₁) (AVL.initLast s)

fromList : List A → ⟨Set⟩
fromList = AVL.fromList ∘ List.map (_, _)

toList : ⟨Set⟩ → List A
toList = List.map proj₁ ∘ AVL.toList

foldr : (A → B → B) → B → ⟨Set⟩ → B
foldr cons nil = AVL.foldr (const ∘′ cons) nil

size : ⟨Set⟩ → ℕ
size = AVL.size

------------------------------------------------------------------------
-- Naïve implementations of union and intersection

union : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
union = AVL.union

unions : List ⟨Set⟩ → ⟨Set⟩
unions = AVL.unions

intersection : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
intersection = AVL.intersection

intersections : List ⟨Set⟩ → ⟨Set⟩
intersections = AVL.intersections

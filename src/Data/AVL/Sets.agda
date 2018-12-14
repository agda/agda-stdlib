------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets, based on AVL trees
------------------------------------------------------------------------

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.Sets
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.Unit
open import Function
open import Level

import Data.AVL strictTotalOrder as AVL
open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

------------------------------------------------------------------------
-- The set type (note that Set is a reserved word)

⟨Set⟩ : Set (a ⊔ ℓ₂)
⟨Set⟩ = AVL.Tree (AVL.const ⊤)

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

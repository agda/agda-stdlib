------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation. This is commonly
-- known as Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional
  {a} {A : Set a} where

open import Data.List.Relation.Binary.Equality.Propositional using (≋⇒≡)
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Re-export definition and operations from setoid sublists

open SetoidSublist (setoid A) public
  hiding
  (lookup; ⊆-reflexive; ⊆-antisym
  ; ⊆-isPreorder; ⊆-isPartialOrder
  ; ⊆-preorder; ⊆-poset
  )

------------------------------------------------------------------------
-- Additional operations

module _ {p} {P : Pred A p} where

  lookup : ∀ {xs ys} → xs ⊆ ys → Any P xs → Any P ys
  lookup = SetoidSublist.lookup (setoid A) (subst _)

------------------------------------------------------------------------
-- Relational properties

⊆-reflexive : _≡_ ⇒ _⊆_
⊆-reflexive refl = ⊆-refl

⊆-antisym : Antisymmetric _≡_ _⊆_
⊆-antisym xs⊆ys ys⊆xs = ≋⇒≡ (SetoidSublist.⊆-antisym (setoid A) xs⊆ys ys⊆xs)

⊆-isPreorder : IsPreorder _≡_ _⊆_
⊆-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ⊆-reflexive
  ; trans         = ⊆-trans
  }

⊆-isPartialOrder : IsPartialOrder _≡_ _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym    = ⊆-antisym
  }

⊆-preorder : Preorder a a a
⊆-preorder = record
  { isPreorder = ⊆-isPreorder
  }

⊆-poset : Poset a a a
⊆-poset = record
  { isPartialOrder = ⊆-isPartialOrder
  }

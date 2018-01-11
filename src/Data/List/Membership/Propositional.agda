------------------------------------------------------------------------
-- The Agda standard library
--
-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

module Data.List.Membership.Propositional where

open import Data.Empty
open import Data.Fin
open import Function.Inverse using (_↔_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any using (Any; map)
import Data.List.Membership.Setoid as Membership
open import Data.List.Relation.Pointwise as ListEq using ([]; _∷_)
open import Data.Product as Prod using (∃; _×_; _,_; uncurry′; proj₂)
open import Relation.Nullary
open import Relation.Binary hiding (Decidable)
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

private module M {a} {A : Set a} = Membership (PropEq.setoid A)
open M public hiding (lose)

lose : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       x ∈ xs → P x → Any P xs
lose {P = P} = M.lose (PropEq.subst P)

-- _⊆_ is a preorder.

⊆-preorder : ∀ {a} → Set a → Preorder _ _ _
⊆-preorder A = Ind.InducedPreorder₂ (PropEq.setoid (List A)) _∈_
                                      (PropEq.subst (_ ∈_))

-- "Equational" reasoning for _⊆_.

module ⊆-Reasoning where
  import Relation.Binary.PreorderReasoning as PreR
  private
    open module PR {a} {A : Set a} = PreR (⊆-preorder A) public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

  infix  1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ {a} {A : Set a} x {xs ys : List A} →
           x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

{-
  infixr 2 _∼⟨_⟩_

  _∼⟨_⟩_ : ∀ {k a} {A : Set a} xs {ys zs : List A} →
           xs ∼[ ⌊ k ⌋→ ] ys → ys IsRelatedTo zs → xs IsRelatedTo zs
  xs ∼⟨ xs≈ys ⟩ ys≈zs = xs ⊆⟨ ⇒→ xs≈ys ⟩ ys≈zs
-}

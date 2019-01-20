------------------------------------------------------------------------
-- The Agda standard library
--
-- First generalizes the idea that an element is the first in a list to
-- satisfy a predicate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.First {a} {A : Set a} where

open import Level using (_⊔_)
open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product as Prod using (∃; -,_; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Unary
open import Relation.Nullary

-----------------------------------------------------------------------
-- Basic type.

module _ {p q} (P : Pred A p) (Q : Pred A q) where

  data First : Pred (List A) (a ⊔ p ⊔ q) where
    [_] : ∀ {x xs} → Q x            → First (x ∷ xs)
    _∷_ : ∀ {x xs} → P x → First xs → First (x ∷ xs)

  data FirstView : Pred (List A) (a ⊔ p ⊔ q) where
    _++_∷_ : ∀ {xs y} → All P xs → Q y → ∀ ys → FirstView (xs List.++ y ∷ ys)

------------------------------------------------------------------------
-- map

module _ {p q r s} {P : Pred A p} {Q : Pred A q} {R : Pred A r} {S : Pred A s} where

  map : P ⊆ R → Q ⊆ S → First P Q ⊆ First R S
  map p⇒r q⇒r [ qx ]      = [ q⇒r qx ]
  map p⇒r q⇒r (px ∷ pqxs) = p⇒r px ∷ map p⇒r q⇒r pqxs

module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

  map₁ : P ⊆ R → First P Q ⊆ First R Q
  map₁ p⇒r = map p⇒r id

  map₂ : Q ⊆ R → First P Q ⊆ First P R
  map₂ = map id

  refine : P ⊆ Q ∪ R → First P Q ⊆ First R Q
  refine f [ qx ]      = [ qx ]
  refine f (px ∷ pqxs) with f px
  ... | inj₁ qx = [ qx ]
  ... | inj₂ rx = rx ∷ refine f pqxs

module _ {p q} {P : Pred A p} {Q : Pred A q} where

------------------------------------------------------------------------
-- Operations

  empty : ¬ First P Q []
  empty ()

  tail : ∀ {x xs} → ¬ Q x → First P Q (x ∷ xs) → First P Q xs
  tail ¬qx [ qx ]      = ⊥-elim (¬qx qx)
  tail ¬qx (px ∷ pqxs) = pqxs

  index : First P Q ⊆ (Fin ∘′ List.length)
  index [ qx ]     = zero
  index (_ ∷ pqxs) = suc (index pqxs)

  index-satisfied : ∀ {xs} (pqxs : First P Q xs) → Q (List.lookup xs (index pqxs))
  index-satisfied [ qx ]     = qx
  index-satisfied (_ ∷ pqxs) = index-satisfied pqxs

  satisfied : ∀ {xs} → First P Q xs → ∃ Q
  satisfied pqxs = -, index-satisfied pqxs

  satisfiable : Satisfiable Q → Satisfiable (First P Q)
  satisfiable (x , qx) = List.[ x ] , [ qx ]

------------------------------------------------------------------------
-- Decidability results

  first : Π[ P ∪ Q ] → Π[ First P Q ∪ All P ]
  first p⊎q []       = inj₂ []
  first p⊎q (x ∷ xs) with p⊎q x
  ... | inj₁ px = Sum.map (px ∷_) (px ∷_) (first p⊎q xs)
  ... | inj₂ qx = inj₁ [ qx ]

------------------------------------------------------------------------
-- Relationship with Any

module _ {q} {Q : Pred A q} where

  fromAny : Any Q ⊆ First U Q
  fromAny (here qx)   = [ qx ]
  fromAny (there any) = _ ∷ fromAny any

  toAny : ∀ {p} {P : Pred A p} → First P Q ⊆ Any Q
  toAny [ qx ]     = here qx
  toAny (_ ∷ pqxs) = there (toAny pqxs)

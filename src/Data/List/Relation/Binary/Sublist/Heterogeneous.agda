------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous sublist relation
-- This is a generalisation of what is commonly known as Order
-- Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL)

module Data.List.Relation.Binary.Sublist.Heterogeneous
  {a b r} {A : Set a} {B : Set b} {R : REL A B r}
  where

open import Level using (_⊔_)

open import Data.List.Base using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Function

open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Re-export core definitions

open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core public

------------------------------------------------------------------------
-- Type and basic combinators

module _ {s} {S : REL A B s} where

  map : R ⇒ S → Sublist R ⇒ Sublist S
  map f []        = []
  map f (y ∷ʳ rs) = y ∷ʳ map f rs
  map f (r ∷ rs)  = f r ∷ map f rs

minimum : Min (Sublist R) []
minimum []       = []
minimum (x ∷ xs) = x ∷ʳ minimum xs

------------------------------------------------------------------------
-- Conversion to and from Any

-- Special case: Sublist R [ a ] bs → Any (R a) bs
toAny : ∀ {a as bs} → Sublist R (a ∷ as) bs → Any (R a) bs
toAny (y ∷ʳ rs) = there (toAny rs)
toAny (r ∷ rs)  = here r

fromAny : ∀ {a bs} → Any (R a) bs → Sublist R [ a ] bs
fromAny (here r)  = r ∷ minimum _
fromAny (there p) = _ ∷ʳ fromAny p

------------------------------------------------------------------------
-- Generalised lookup based on a proof of Any

module _ {p q} {P : Pred A p} {Q : Pred B q} (resp : P ⟶ Q Respects R) where

  lookup : ∀ {xs ys} → Sublist R xs ys → Any P xs → Any Q ys
  lookup (y ∷ʳ p)  k         = there (lookup p k)
  lookup (rxy ∷ p) (here px) = here (resp rxy px)
  lookup (rxy ∷ p) (there k) = there (lookup p k)

------------------------------------------------------------------------
-- Disjoint sublists xs,ys ⊆ zs
--
-- NB: This does not imply that xs and ys partition zs;
-- zs may have additional elements.

private
  infix 4 _⊆_
  _⊆_ = Sublist R

infixr 5 _∷ₙ_ _∷ₗ_ _∷ᵣ_

data Disjoint : ∀ {xs ys zs} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → Set (a ⊔ b ⊔ r) where
  []   : Disjoint [] []

  -- Element y of zs is neither in xs nor in ys:
  _∷ₙ_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
         (y : B)       → Disjoint τ₁ τ₂ → Disjoint (y  ∷ʳ τ₁) (y  ∷ʳ τ₂)

  -- Element y of zs is in xs as x with x≈y:
  _∷ₗ_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {x y} →
         (x≈y : R x y) → Disjoint τ₁ τ₂ → Disjoint (x≈y ∷ τ₁) (y  ∷ʳ τ₂)

  -- Element y of zs is in ys as x with x≈y:
  _∷ᵣ_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {x y} →
         (x≈y : R x y) → Disjoint τ₁ τ₂ → Disjoint (y  ∷ʳ τ₁) (x≈y ∷ τ₂)

------------------------------------------------------------------------
-- Disjoint union of two sublists xs,ys ⊆ zs
--
-- This is the Cover relation without overlap of Section 6 of
-- Conor McBride, Everybody's Got To Be Somewhere,
-- MSFP@FSCD 2018: 53-69.

data DisjointUnion : ∀ {xs ys zs us} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) (τ : us ⊆ zs) →  Set (a ⊔ b ⊔ r) where
  []   : DisjointUnion [] [] []

  -- Element y of zs is neither in xs nor in ys: skip.
  _∷ₙ_ : ∀ {xs ys zs us} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : us ⊆ zs} →
         (y : B)       → DisjointUnion τ₁ τ₂ τ → DisjointUnion (y  ∷ʳ τ₁) (y  ∷ʳ τ₂) (y ∷ʳ τ)

  -- Element y of zs is in xs as x with x≈y: add to us.
  _∷ₗ_ : ∀ {xs ys zs us} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : us ⊆ zs} {x y} →
         (x≈y : R x y) → DisjointUnion τ₁ τ₂ τ → DisjointUnion (x≈y ∷ τ₁) (y  ∷ʳ τ₂) (x≈y ∷ τ)

  -- Element y of zs is in ys as x with x≈y: add to us.
  _∷ᵣ_ : ∀ {xs ys zs us} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : us ⊆ zs} {x y} →
         (x≈y : R x y) → DisjointUnion τ₁ τ₂ τ → DisjointUnion (y  ∷ʳ τ₁) (x≈y ∷ τ₂) (x≈y ∷ τ)

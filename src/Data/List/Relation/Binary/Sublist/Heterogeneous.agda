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

toAny : ∀ {a bs} → Sublist R [ a ] bs → Any (R a) bs
toAny (y ∷ʳ rs) = there (toAny rs)
toAny (r ∷ rs)  = here r

fromAny : ∀ {a bs} → Any (R a) bs → Sublist R [ a ] bs
fromAny (here r)  = r ∷ minimum _
fromAny (there p) = _ ∷ʳ fromAny p

------------------------------------------------------------------------
-- Generalised lookup based on a proof of Any

module _ {p q} {P : Pred A p} {Q : Pred B q} (resp : P ⟶ Q Respects R) where

  lookup : ∀ {xs ys} → Sublist R xs ys → Any P xs → Any Q ys
  lookup []       ()
  lookup (y ∷ʳ p)  k         = there (lookup p k)
  lookup (rxy ∷ p) (here px) = here (resp rxy px)
  lookup (rxy ∷ p) (there k) = there (lookup p k)

------------------------------------------------------------------------
-- The Agda standard library
--
-- All predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.All where

open import Level using (Level; _⊔_; Lift)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh

private
  variable
    a b p q r : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r

module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  data All : List# A R → Set (p ⊔ a ⊔ r) where
    []  : All []
    _∷_ : ∀ {x xs pr} → P x → All xs → All (cons x xs pr)

map : {xs : List# A R} → ∀[ P ⇒ Q ] → All P xs → All Q xs
map p⇒q []       = []
map p⇒q (p ∷ ps) = p⇒q p ∷ map p⇒q ps

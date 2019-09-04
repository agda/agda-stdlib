------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of fresh lists and functions acting on them
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Properties where

open import Level using (Level; _⊔_; Lift)
open import Relation.Nullary
open import Relation.Unary as U using (Pred)
open import Relation.Binary as B using (Rel)


open import Data.List.Fresh

private
  variable
    a b p r : Level
    A : Set a
    B : Set b
    R : Rel A r

------------------------------------------------------------------------
-- Empty and NotEmpty

Empty⇒¬NonEmpty : {xs : List# A R} → Empty xs → ¬ (NonEmpty xs)
Empty⇒¬NonEmpty [] ()

NonEmpty⇒¬Empty : {xs : List# A R} → NonEmpty xs → ¬ (Empty xs)
NonEmpty⇒¬Empty () []

empty? : (xs : List# A R) → Dec (Empty xs)
empty? []       = yes []
empty? (_ ∷# _) = no (λ ())

nonEmpty? : (xs : List# A R) → Dec (NonEmpty xs)
nonEmpty? []             = no (λ ())
nonEmpty? (cons x xs pr) = yes (cons x xs pr)

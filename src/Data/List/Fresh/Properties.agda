------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of fresh lists and functions acting on them
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Product using (_,_)
open import Relation.Nullary
open import Relation.Unary as U using (Pred)
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh

private
  variable
    a b e p r : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Fresh congruence

module _ {R : Rel A r} {_≈_ : Rel A e} (R≈ : R B.Respectsˡ _≈_) where

  fresh-respectsˡ : ∀ {x y} {xs : List# A R} → x ≈ y → x # xs → y # xs
  fresh-respectsˡ {xs = []}      x≈y x#xs       = _
  fresh-respectsˡ {xs = x ∷# xs} x≈y (r , x#xs) =
    R≈ x≈y r , fresh-respectsˡ x≈y x#xs

------------------------------------------------------------------------
-- Empty and NotEmpty

Empty⇒¬NonEmpty : {R : Rel A r} {xs : List# A R} → Empty xs → ¬ (NonEmpty xs)
Empty⇒¬NonEmpty [] ()

NonEmpty⇒¬Empty : {R : Rel A r} {xs : List# A R} → NonEmpty xs → ¬ (Empty xs)
NonEmpty⇒¬Empty () []

empty? : {R : Rel A r} (xs : List# A R) → Dec (Empty xs)
empty? []       = yes []
empty? (_ ∷# _) = no (λ ())

nonEmpty? : {R : Rel A r} (xs : List# A R) → Dec (NonEmpty xs)
nonEmpty? []             = no (λ ())
nonEmpty? (cons x xs pr) = yes (cons x xs pr)

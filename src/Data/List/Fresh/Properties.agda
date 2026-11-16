------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of fresh lists and functions acting on them
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Properties where

open import Data.List.Fresh using (List#; _∷#_; _#_; Empty; NonEmpty; cons; [])
open import Data.Product.Base using (_,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Definitions as Binary using (_Respects_; _Respectsˡ_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a b ℓ p r : Level
    A : Set a
    B : Set b
    R : Rel A r
    x y : A
    xs : List# A R


------------------------------------------------------------------------
-- Fresh congruence

module _ {_≈_ : Rel A ℓ} (resp : R Respectsˡ _≈_) where

  fresh-respectsˡ : ∀ {xs : List# A R} → (_# xs) Respects _≈_
  fresh-respectsˡ {xs = []}      x≈y _          = _
  fresh-respectsˡ {xs = x ∷# xs} x≈y (r , x#xs) =
    resp x≈y r , fresh-respectsˡ x≈y x#xs

------------------------------------------------------------------------
-- Empty and NotEmpty

Empty⇒¬NonEmpty : Empty xs → ¬ (NonEmpty xs)
Empty⇒¬NonEmpty [] ()

NonEmpty⇒¬Empty : NonEmpty xs → ¬ (Empty xs)
NonEmpty⇒¬Empty () []

empty? : (xs : List# A R) → Dec (Empty xs)
empty? []       = yes []
empty? (_ ∷# _) = no λ()

nonEmpty? : (xs : List# A R) → Dec (NonEmpty xs)
nonEmpty? []             = no λ()
nonEmpty? (cons x xs pr) = yes (cons x xs pr)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.Any.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh
open import Data.List.Fresh.Relation.Unary.Any

private
  variable
    a b p q r : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r

------------------------------------------------------------------------
-- NonEmpty

Any⇒NonEmpty : {xs : List# A R} → Any P xs → NonEmpty xs
Any⇒NonEmpty {xs = cons x xs pr} p  = cons x xs pr

------------------------------------------------------------------------
-- remove

length-remove : {xs : List# A R} (k : Any P xs) →
  length xs ≡ suc (length (xs ─ k))
length-remove (here _)  = refl
length-remove (there p) = cong suc (length-remove p)

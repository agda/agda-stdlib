------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.All.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘′_)
open import Relation.Nullary
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)
open import Data.List.Fresh.Relation.Unary.All

private
  variable
    a b p q r s : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r
    S : Rel A s


fromAll : ∀ {x} {xs : List# A R} → All (R x) xs → x # xs
fromAll []       = _
fromAll (p ∷ ps) = p , fromAll ps

toAll : ∀ {x} {xs : List# A R} → x # xs → All (R x) xs
toAll {xs = []}      _        = []
toAll {xs = a ∷# as} (p , ps) = p ∷ toAll ps

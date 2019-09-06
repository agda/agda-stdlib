------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Fresh.Membership.Setoid.Properties {c ℓ} (S : Setoid c ℓ) where

open import Level using (Level; _⊔_)
open import Data.List.Fresh
open import Data.List.Fresh.Membership.Setoid S
open import Relation.Nullary
open import Relation.Unary as U using (Pred)

open import Data.List.Fresh.Relation.Unary.Any using (Any; here; there)
import Data.List.Fresh.Relation.Unary.Any.Properties as Anyₚ
import Data.List.Fresh.Relation.Unary.All.Properties as Allₚ

open Setoid S renaming (Carrier to A)

private
  variable
    p r : Level

------------------------------------------------------------------------
-- Transport

≈-subst-∈ : ∀ {R : Rel A r} {x y} {xs : List# A R} → x ≈ y → x ∈ xs → y ∈ xs
≈-subst-∈ x≈y (here x≈x′)  = here (trans (sym x≈y) x≈x′)
≈-subst-∈ x≈y (there x∈xs) = there (≈-subst-∈ x≈y x∈xs)

------------------------------------------------------------------------
-- Disjointness

distinct : ∀ {R : Rel A r} {x y} {xs : List# A R} → x ∈ xs → y ∉ xs → x ≉ y
distinct x∈xs y∉xs x≈y = y∉xs (≈-subst-∈ x≈y x∈xs)

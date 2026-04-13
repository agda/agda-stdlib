------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidability of the disjoint relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Disjoint.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Data.Product.Base using (_,_)
open import Data.List.Relation.Unary.Any using (map)
open import Data.List.Relation.Unary.All using (all?; lookupₛ)
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no; decidable-stable)
open DecSetoid S
open import Data.List.Relation.Binary.Equality.DecSetoid S
open import Data.List.Relation.Binary.Disjoint.Setoid setoid public
open import Data.List.Membership.DecSetoid S

disjoint? : Decidable Disjoint
disjoint? xs ys with all? (_∉? ys) xs
... | yes xs♯ys = yes λ (v∈ , v∈′) →
  lookupₛ setoid (λ x≈y ∉ys ∈ys → ∉ys (map (trans x≈y) ∈ys)) xs♯ys v∈ v∈′
... | no ¬xs♯ys = let (x , x∈ , ¬∉ys) = find (¬All⇒Any¬ (_∉? _) _ ¬xs♯ys) in
  no λ p → p (x∈ , decidable-stable (_ ∈? _) ¬∉ys)

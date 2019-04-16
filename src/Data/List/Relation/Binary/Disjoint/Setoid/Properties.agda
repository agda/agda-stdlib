------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of disjoint lists (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Disjoint.Setoid.Properties where

open import Data.List
open import Data.List.Relation.Binary.Disjoint.Setoid
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

module _ {c ℓ} (S : Setoid c ℓ) where

  sym : Symmetric (Disjoint S)
  sym xs#ys (v∈ys , v∈xs) = xs#ys (v∈xs , v∈ys)

------------------------------------------------------------------------
-- Relationship with other predicates
------------------------------------------------------------------------

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S

  Disjoint⇒AllAll : ∀ {xs ys} → Disjoint S xs ys →
                    All (λ x → All (λ y → ¬ x ≈ y) ys) xs
  Disjoint⇒AllAll xs#ys = All.map (¬Any⇒All¬ _)
    (All.tabulate (λ v∈xs v∈ys → xs#ys (Any.map reflexive v∈xs , v∈ys)))

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- concat

module _ {c ℓ} (S : Setoid c ℓ) where

  concat⁺ʳ : ∀ {vs xss} → All (Disjoint S vs) xss → Disjoint S vs (concat xss)
  concat⁺ʳ {xss = []}       []               (_ , ())
  concat⁺ʳ {xss = xs ∷ xss} (vs#xs ∷ vs#xss) (v∈vs , v∈xs++concatxss)
    with ++⁻ xs v∈xs++concatxss
  ... | inj₁ v∈xs  = vs#xs (v∈vs , v∈xs)
  ... | inj₂ v∈xss = concat⁺ʳ vs#xss (v∈vs , v∈xss)

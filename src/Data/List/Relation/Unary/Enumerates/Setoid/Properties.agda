------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lists which contain every element of a given type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin hiding (_≟_)
open import Data.List.Base
open import Data.List.Membership.Setoid.Properties as Membership
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Unary.Enumerates.Setoid
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise
  using (_⊎ₛ_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (_×ₛ_)
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Properties.Setoid using (respʳ-flip)

module Data.List.Relation.Unary.Enumerates.Setoid.Properties where

open Setoid

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- map

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) (surj : Surjection S T) where
  open Surjection surj

  map⁺ : ∀ {xs} → IsEnumeration S xs → IsEnumeration T (map f xs)
  map⁺ _∈xs y with surjective y
  ... | (x , fx≈y) = ∈-resp-≈ T fx≈y (∈-map⁺ S T cong (x ∈xs))

------------------------------------------------------------------------
-- _++_

module _ (S : Setoid a ℓ₁) where

  ++⁺ˡ : ∀ {xs} ys → IsEnumeration S xs → IsEnumeration S (xs ++ ys)
  ++⁺ˡ _ _∈xs v = Membership.∈-++⁺ˡ S (v ∈xs)

  ++⁺ʳ : ∀ xs {ys} → IsEnumeration S ys → IsEnumeration S (xs ++ ys)
  ++⁺ʳ _ _∈ys v = Membership.∈-++⁺ʳ S _ (v ∈ys)

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  ++⁺ : ∀ {xs ys} → IsEnumeration S xs → IsEnumeration T ys →
        IsEnumeration (S ⊎ₛ T) (map inj₁ xs ++ map inj₂ ys)
  ++⁺ _∈xs _ (inj₁ x) = ∈-++⁺ˡ (S ⊎ₛ T)   (∈-map⁺ S (S ⊎ₛ T) inj₁ (x ∈xs))
  ++⁺ _ _∈ys (inj₂ y) = ∈-++⁺ʳ (S ⊎ₛ T) _ (∈-map⁺ T (S ⊎ₛ T) inj₂ (y ∈ys))

------------------------------------------------------------------------
-- cartesianProduct

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  cartesianProduct⁺ : ∀ {xs ys} → IsEnumeration S xs → IsEnumeration T ys →
                      IsEnumeration (S ×ₛ T) (cartesianProduct xs ys)
  cartesianProduct⁺ _∈xs _∈ys (x , y) = ∈-cartesianProduct⁺ S T (x ∈xs) (y ∈ys)

------------------------------------------------------------------------
-- deduplicate

module _ (S? : DecSetoid a ℓ₁) where
  open DecSetoid S? renaming (setoid to S)

  deduplicate⁺ : ∀ {xs} → IsEnumeration S xs →
                 IsEnumeration S (deduplicate _≟_ xs)
  deduplicate⁺ = ∈-deduplicate⁺ S _≟_ (respʳ-flip S) ∘_

------------------------------------------------------------------------
-- lookup

module _ (S : Setoid a ℓ₁) where

  lookup-surjective : ∀ {xs} → IsEnumeration S xs →
                      Surjective {A = Fin (length xs)} _≡_ (_≈_ S) (lookup xs)
  lookup-surjective _∈xs y = index (y ∈xs) , sym S (lookup-index (y ∈xs))

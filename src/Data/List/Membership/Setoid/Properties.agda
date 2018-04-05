------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.Fin using (Fin)
import Data.List.Any.Properties as Any
open import Data.Maybe using (Maybe)
open import Data.Nat using (_<_)
import Data.List.Membership.Setoid as Membership
import Data.List.Relation.Equality.Setoid as Equality
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Function using (flip)
open import Relation.Binary

module Data.List.Membership.Setoid.Properties where

------------------------------------------------------------------------
-- Equality properties

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S
  open Equality S
  open import Data.List.Membership.Setoid S

  -- Equality is respected by the predicate which is used to define _∈_.

  ∈-resp-≈ : ∀ {x} → (x ≈_) Respects _≈_
  ∈-resp-≈ = flip trans

  -- List equality is respected by _∈_.

  ∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
  ∈-resp-≋ = Any.lift-resp ∈-resp-≈

------------------------------------------------------------------------
-- map

module _ {c₁ c₂ ℓ₁ ℓ₂} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

  open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; refl to refl₁)
  open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_)
  open Membership S₁ using (find) renaming (_∈_ to _∈₁_)
  open Membership S₂ using () renaming (_∈_ to _∈₂_)

  ∈-map⁺ : ∀ {f} → f Preserves _≈₁_ ⟶ _≈₂_ → ∀ {x xs} →
            x ∈₁ xs → f x ∈₂ map f xs
  ∈-map⁺ pres x∈xs = Any.map⁺ (Any.map pres x∈xs)

  ∈-map⁻ : ∀ {y xs f} → y ∈₂ map f xs →
           ∃ λ x → x ∈₁ xs × y ≈₂ f x
  ∈-map⁻ x∈map = find (Any.map⁻ x∈map)

------------------------------------------------------------------------
-- mapMaybe

-- ?

------------------------------------------------------------------------
-- _++_

module _ {c ℓ} (S : Setoid c ℓ) where

  open Membership S using (_∈_)

  ∈-++⁺ˡ : ∀ {v xs ys} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ = Any.++⁺ˡ

  ∈-++⁺ʳ : ∀ {v} xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = Any.++⁺ʳ

  ∈-++⁻ : ∀ {v} xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
  ∈-++⁻ = Any.++⁻

------------------------------------------------------------------------
-- concat

module _ {c ℓ} (S : Setoid c ℓ) where

  open Membership S using (_∈_)

  -- ?

------------------------------------------------------------------------
-- applyUpTo

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S using (_≈_; refl)
  open Membership S using (_∈_)

  ∈-applyUpTo⁺ : ∀ f {i n} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ f = Any.applyUpTo⁺ f refl

  ∈-applyUpTo⁻ : ∀ {v} f {n} → v ∈ applyUpTo f n →
                 ∃ λ i → i < n × v ≈ f i
  ∈-applyUpTo⁻ = Any.applyUpTo⁻

------------------------------------------------------------------------
-- tabulate

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S using (_≈_; refl) renaming (Carrier to A)
  open Membership S using (_∈_)

  tabulate⁺ : ∀ {n} {f : Fin n → A} i → f i ∈ tabulate f
  tabulate⁺ i = Any.tabulate⁺ i refl

  tabulate⁻ : ∀ {n} {f : Fin n → A} {v} →
              v ∈ tabulate f → ∃ λ i → v ≈ f i
  tabulate⁻ = Any.tabulate⁻

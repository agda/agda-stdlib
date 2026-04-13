------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique lists (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Unique.Setoid.Properties where

open import Data.List.Base
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Binary.Disjoint.Setoid
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Unique.Setoid
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_<_)
open import Function.Base using (_∘_; id)
open import Function.Definitions using (Congruent; Injective)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_; contraposition)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level


------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ (S : Setoid a ℓ₁) (R : Setoid b ℓ₂) where

  open Setoid S renaming (_≈_ to _≈₁_)
  open Setoid R renaming (_≈_ to _≈₂_)

  map⁺ : ∀ {f} → Injective _≈₁_ _≈₂_ f →
         ∀ {xs} → Unique S xs → Unique R (map f xs)
  map⁺ inj xs! = AllPairs.map⁺ (AllPairs.map (contraposition inj) xs!)

  map⁻ : ∀ {f} → Congruent _≈₁_ _≈₂_ f →
         Unique R ∘ map f ⊆ Unique S
  map⁻ cong fxs! = AllPairs.map (contraposition cong) (AllPairs.map⁻ fxs!)

------------------------------------------------------------------------
-- ++

module _ (S : Setoid a ℓ) where

  ++⁺ : ∀ {xs ys} → Unique S xs → Unique S ys → Disjoint S xs ys → Unique S (xs ++ ys)
  ++⁺ xs! ys! xs#ys = AllPairs.++⁺ xs! ys! (Disjoint⇒AllAll S xs#ys)

------------------------------------------------------------------------
-- concat

module _ (S : Setoid a ℓ) where

  concat⁺ : ∀ {xss} → All (Unique S) xss → AllPairs (Disjoint S) xss → Unique S (concat xss)
  concat⁺ xss! xss# = AllPairs.concat⁺ xss! (AllPairs.map (Disjoint⇒AllAll S) xss#)

------------------------------------------------------------------------
-- cartesianProductWith

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) (U : Setoid c ℓ₃) where

  open Setoid S using () renaming (_≈_ to _≈₁_)
  open Setoid T using () renaming (_≈_ to _≈₂_)
  open Setoid U using () renaming (_≈_ to _≈₃_; sym to sym₃; trans to trans₃)

  cartesianProductWith⁺ : ∀ {xs ys} f → (∀ {w x y z} → f w y ≈₃ f x z → w ≈₁ x × y ≈₂ z) →
                          Unique S xs → Unique T ys →
                          Unique U (cartesianProductWith f xs ys)
  cartesianProductWith⁺ {_}      {_}  f f-inj  []          ys! = [] {S = U}
  cartesianProductWith⁺ {x ∷ xs} {ys} f f-inj (x∉xs ∷ xs!) ys! = ++⁺ U
    (map⁺ T U (proj₂ ∘ f-inj) ys!)
    (cartesianProductWith⁺ f f-inj xs! ys!)
    map#cartesianProductWith
    where
    map#cartesianProductWith : Disjoint U (map (f x) ys) (cartesianProductWith f xs ys)
    map#cartesianProductWith (v∈map , v∈com) with
      ∈-map⁻ T U v∈map | ∈-cartesianProductWith⁻ S T U f xs ys v∈com
    ... | (c , _ , v≈fxc) | (a , b , a∈xs , _ , v≈fab) =
      All¬⇒¬Any x∉xs (∈-resp-≈ S (proj₁ (f-inj (trans₃ (sym₃ v≈fab) v≈fxc))) a∈xs)

------------------------------------------------------------------------
-- cartesianProduct

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) {xs ys} where

  cartesianProduct⁺ : Unique S xs → Unique T ys →
                      Unique (S ×ₛ T) (cartesianProduct xs ys)
  cartesianProduct⁺ = cartesianProductWith⁺ S T (S ×ₛ T) _,_ id

------------------------------------------------------------------------
-- take & drop

module _ (S : Setoid a ℓ) where

  drop⁺ : ∀ {xs} n → Unique S xs → Unique S (drop n xs)
  drop⁺ = AllPairs.drop⁺

  take⁺ : ∀ {xs} n → Unique S xs → Unique S (take n xs)
  take⁺ = AllPairs.take⁺

------------------------------------------------------------------------
-- applyUpTo

module _ (S : Setoid a ℓ) where

  open Setoid S

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → f i ≉ f j) →
                Unique S (applyUpTo f n)
  applyUpTo⁺₁ = AllPairs.applyUpTo⁺₁

  applyUpTo⁺₂ : ∀ f n → (∀ i j → f i ≉ f j) →
                Unique S (applyUpTo f n)
  applyUpTo⁺₂ = AllPairs.applyUpTo⁺₂

------------------------------------------------------------------------
-- applyDownFrom

module _ (S : Setoid a ℓ) where

  open Setoid S

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → f i ≉ f j) →
                    Unique S (applyDownFrom f n)
  applyDownFrom⁺₁ = AllPairs.applyDownFrom⁺₁

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → f i ≉ f j) →
                    Unique S (applyDownFrom f n)
  applyDownFrom⁺₂ = AllPairs.applyDownFrom⁺₂

------------------------------------------------------------------------
-- tabulate

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → f i ≈ f j → i ≡ j) →
              Unique S (tabulate f)
  tabulate⁺ f-inj = AllPairs.tabulate⁺ (_∘ f-inj)

------------------------------------------------------------------------
-- filter

module _ (S : Setoid a ℓ) {P : Pred _ p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → Unique S xs → Unique S (filter P? xs)
  filter⁺ = AllPairs.filter⁺ P?

------------------------------------------------------------------------
-- ∷

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  open Membership S using (_∉_)

  private
    variable
      x y : A
      xs : List A

  Unique[x∷xs]⇒x∉xs : Unique S (x ∷ xs) → x ∉ xs
  Unique[x∷xs]⇒x∉xs ((x≉ ∷ x∉) ∷ _ ∷ uniq) = λ where
    (here x≈)  → x≉ x≈
    (there x∈) → Unique[x∷xs]⇒x∉xs (x∉ AllPairs.∷ uniq) x∈

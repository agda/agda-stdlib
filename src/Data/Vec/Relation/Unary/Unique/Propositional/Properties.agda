------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique vectors (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.Unique.Propositional.Properties where

open import Data.Vec.Base using (Vec; map; take; drop; tabulate; lookup)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
import Data.Vec.Relation.Unary.Unique.Setoid.Properties as Setoid
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_+_)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡⇒≡×≡)
open import Function.Base using (id; _∘_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core
  using (refl; _≡_; _≢_; sym)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    a b c p : Level

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {A : Set a} {B : Set b} where

  map⁺ : ∀ {f} → (∀ {x y} → f x ≡ f y → x ≡ y) →
         ∀ {n} {xs : Vec A n} → Unique xs → Unique (map f xs)
  map⁺ = Setoid.map⁺ (setoid A) (setoid B)

------------------------------------------------------------------------
-- take & drop

module _ {A : Set a} where

  drop⁺ : ∀ {n} m {xs : Vec A (m + n)} → Unique xs → Unique (drop m xs)
  drop⁺ = Setoid.drop⁺ (setoid A)

  take⁺ : ∀ {n} m {xs : Vec A (m + n)} → Unique xs → Unique (take m xs)
  take⁺ = Setoid.take⁺ (setoid A)

------------------------------------------------------------------------
-- tabulate

module _ {A : Set a} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → f i ≡ f j → i ≡ j) → Unique (tabulate f)
  tabulate⁺ = Setoid.tabulate⁺ (setoid A)

------------------------------------------------------------------------
-- lookup

module _ {A : Set a} where

  lookup-injective : ∀ {n} {xs : Vec A n} → Unique xs → ∀ i j → lookup xs i ≡ lookup xs j → i ≡ j
  lookup-injective = Setoid.lookup-injective (setoid A)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Predomain.Structures
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where

import Data.Empty.Polymorphic as Empty
open import Function.Base using (_on_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Definitions
open import Relation.Binary.Predomain.Definitions

open import Relation.Binary.Structures _≈_
  using (IsPreorder; IsPartialOrder)

private
  variable
    i ℓ′ : Level
    I : Set i
    x : A


------------------------------------------------------------------------
-- Directed-complete Preorders
------------------------------------------------------------------------

record IsDCPreorder {i} (_≲_ : Rel A ℓ′) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ suc i) where
  field
    isPreorder : IsPreorder _≲_
    _≲⋁[_]_   : ∀ {I : Set i} (x : A) (f : I → A) → Directed (_≲_ on f) → A
    ≲⋁-isMub  : ∀ {I : Set i} (x : A) (f : I → A) (d : Directed (_≲_ on f)) →
                MinimalUpperBoundAbove _≲_ f x (x ≲⋁[ f ] d)

  module _ {I : Set i} {x : A} {f : I → A} {d : Directed (_≲_ on f)} where

    open MinimalUpperBoundAbove (≲⋁-isMub x f d) public
      renaming (lowerBound to ≲⋁; upperBound to ≲ᶠ⋁; minimal to ≲⋁-minimal)


record IsDCPartialOrder {i} (_≤_ : Rel A ℓ′) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ suc i) where
  field
    isDCPreorder : IsDCPreorder {i = i} _≤_
    antisym      : Antisymmetric _≈_ _≤_

  open IsDCPreorder isDCPreorder public
    renaming (_≲⋁[_]_ to _≤⋁[_]_; ≲⋁-isMub to ≤⋁-isMub
             ; ≲⋁ to ≤⋁; ≲ᶠ⋁ to ≤ᶠ⋁; ≲⋁-minimal to ≤⋁-minimal)

  isPartialOrder : IsPartialOrder _≤_
  isPartialOrder = record { isPreorder = isPreorder ; antisym = antisym }

  open IsPartialOrder isPartialOrder public
    hiding (antisym)

  _≤⋁[∅] : A → A
  x ≤⋁[∅] = _≤⋁[_]_ {I = Empty.⊥ {i}} x (λ()) λ()

  x≤⋁[∅]≈x : (x ≤⋁[∅]) ≈ x
  x≤⋁[∅]≈x = antisym (≤⋁-minimal refl λ()) ≤⋁


record IsDomain {i} (_≤_ : Rel A ℓ′) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ suc i) where
  field
    isDCPartialOrder : IsDCPartialOrder {i = i} _≤_
    ⊥ : A
    ⊥-minimal : ∀ {x} → ⊥ ≤ x

  open IsDCPartialOrder isDCPartialOrder public

  ⊥-least : ∀ {x} → x ≤ ⊥ → x ≈ ⊥
  ⊥-least x≤⊥ = antisym x≤⊥ ⊥-minimal

  ⋁[∅] : A
  ⋁[∅] = ⊥ ≤⋁[∅]
  
  ⋁[∅]≈⊥ : ⋁[∅] ≈ ⊥
  ⋁[∅]≈⊥ = x≤⋁[∅]≈x

  ⋁[_]_ : ∀ {I : Set i} (f : I → A) → Directed (_≤_ on f) → A
  ⋁[_]_ = ⊥ ≤⋁[_]_

  ⋁-minimal : ∀ {I : Set i} {f : I → A} {d :  Directed (_≤_ on f)} {z} →
               UpperBound _≤_ f z → (⋁[ f ] d) ≤ z
  ⋁-minimal = ≤⋁-minimal ⊥-minimal

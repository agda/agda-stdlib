------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL Maps identifying values up to
-- propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Map.Membership.Propositional
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Product.Base using (_×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using ()
  renaming (Pointwise to _×ᴿ_)
open import Level using (Level)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_)

open StrictTotalOrder strictTotalOrder using (_≈_) renaming (Carrier to Key)
open import Data.Tree.AVL.Map strictTotalOrder using (Map)
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder using (Any)


private
  variable
    v : Level
    V : Set v
    m : Map V
    kx : Key × V

infix 4 _≈ₖᵥ_

_≈ₖᵥ_ : Rel (Key × V) _
_≈ₖᵥ_ = _≈_ ×ᴿ _≡_

------------------------------------------------------------------------
-- Membership: ∈ₖᵥ

infix 4 _∈ₖᵥ_ _∉ₖᵥ_

_∈ₖᵥ_ : Key × V → Map V → Set _
kx ∈ₖᵥ m = Any (_≈ₖᵥ_ kx) m

_∉ₖᵥ_ : Key × V → Map V → Set _
kx ∉ₖᵥ m = ¬ kx ∈ₖᵥ m

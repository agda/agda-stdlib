------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL Maps identifying values up to
-- propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Map.Membership.Propositional
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (just; nothing; is-just)
open import Data.Product as Prod using (_×_; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent renaming (Pointwise to _×ᴿ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _∘′_)
open import Level using (Level)

open import Relation.Binary using (Transitive; Symmetric; _Respectsˡ_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Intersection using (_∩_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (Reflects; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key) hiding (trans)
open Eq using (_≉_; refl; sym; trans)
open import Data.Tree.AVL strictTotalOrder using (tree)
open import Data.Tree.AVL.Indexed strictTotalOrder using (key)
import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder as IAny
import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties strictTotalOrder as IAnyₚ
open import Data.Tree.AVL.Key strictTotalOrder using (⊥⁺<[_]<⊤⁺)
open import Data.Tree.AVL.Map strictTotalOrder
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder as Mapₚ using (Any)
open import Data.Tree.AVL.Relation.Unary.Any strictTotalOrder as Any using (tree)

private
  variable
    v p q : Level
    V : Set v
    m : Map V
    k k′ : Key
    x x′ y y′ : V
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

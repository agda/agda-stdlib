------------------------------------------------------------------------
-- The Agda standard library
--
-- Substituting equalities for binary relations
------------------------------------------------------------------------

-- For more general transformations between binary relations
-- see `Relation.Binary.Morphisms`.

{-# OPTIONS --without-K --safe #-}

open import Data.Product as Prod
open import Relation.Binary

module Relation.Binary.Construct.Subst.Equality
  {a ℓ₁ ℓ₂} {A : Set a} {≈₁ : Rel A ℓ₁} {≈₂ : Rel A ℓ₂}
  (equiv@(to , from) : ≈₁ ⇔ ≈₂)
  where

open import Function.Base

------------------------------------------------------------------------
-- Definitions

refl : Reflexive ≈₁ → Reflexive ≈₂
refl refl = to refl

sym : Symmetric ≈₁ → Symmetric ≈₂
sym sym = to ∘′ sym ∘′ from

trans : Transitive ≈₁ → Transitive ≈₂
trans trans x≈y y≈z = to (trans (from x≈y) (from y≈z))

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence ≈₁ → IsEquivalence ≈₂
isEquivalence E = record
  { refl  = refl  E.refl
  ; sym   = sym   E.sym
  ; trans = trans E.trans
  } where module E = IsEquivalence E

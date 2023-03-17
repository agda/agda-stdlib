------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures where the carrier is ⊥.
-- In mathematics, this is usually called 0.
--
-- From monoids up, these are zero-objects – i.e, the initial
-- object is the terminal object in the relevant category.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level)

module Algebra.Construct.Initial {c ℓ : Level} where

open import Algebra.Bundles
  using (Magma; Semigroup; Band)
open import Algebra.Bundles.Raw
  using (RawMagma)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Congruent₂)
open import Algebra.Structures using (IsMagma; IsSemigroup; IsBand)
open import Data.Empty.Polymorphic
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence)


------------------------------------------------------------------------
-- Re-export those algebras which are also terminal

open import Algebra.Construct.Terminal {c} {ℓ} public
  hiding (rawMagma; magma; semigroup; band)

------------------------------------------------------------------------
-- Gather all the functionality in one place

module ℤero where

  infixl 7 _∙_
  infix  4 _≈_

  Carrier : Set c
  Carrier = ⊥

  _≈_     : Rel Carrier ℓ
  _≈_ ()

  _∙_     : Op₂ Carrier
  _∙_ ()

  refl : Reflexive _≈_
  refl {x = ()}

  sym : Symmetric _≈_
  sym {x = ()}

  trans : Transitive _≈_
  trans {i = ()}

  ∙-cong : Congruent₂ _≈_ _∙_
  ∙-cong {x = ()}

open ℤero

------------------------------------------------------------------------
-- Raw bundles

rawMagma : RawMagma c ℓ
rawMagma = record { ℤero }

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence _≈_
isEquivalence = record { ℤero }

isMagma : IsMagma _≈_ _∙_
isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

isSemigroup : IsSemigroup _≈_ _∙_
isSemigroup = record { isMagma = isMagma ; assoc = λ () }

isBand : IsBand _≈_ _∙_
isBand = record { isSemigroup = isSemigroup ; idem = λ () }

------------------------------------------------------------------------
-- Bundles

magma : Magma c ℓ
magma = record { isMagma = isMagma }

semigroup : Semigroup c ℓ
semigroup = record { isSemigroup = isSemigroup }

band : Band c ℓ
band = record { isBand = isBand }


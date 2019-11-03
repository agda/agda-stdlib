------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Homogeneous`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Homogeneous.Core where

open import Level using (Level; _⊔_)
open import Data.Product using (_×_)
open import Relation.Binary as B using (REL; Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Indexed.Heterogeneous as I
open import Relation.Unary.Indexed using (IPred)

private
  variable
    a b c ℓ : Level
    I : Set c

------------------------------------------------------------------------
-- Homegeneously indexed binary relations

-- Heterogeneous types

IREL : (I → Set a) → (I → Set b) → (ℓ : Level) → Set _
IREL A B ℓ = ∀ {i} → REL (A i) (B i) ℓ

-- Homogeneous types

IRel : (I → Set a) → (ℓ : Level) → Set _
IRel A = IREL A A

------------------------------------------------------------------------
-- Lifting to non-indexed binary relations

-- Ideally this should be in: `Construct.Lift` but we want this relation
-- to be exported by the various structures & bundles.

Lift : (A : I → Set a) → IRel A ℓ → Rel (∀ i → A i) _
Lift _ _∼_ x y = ∀ i → x i ∼ y i

------------------------------------------------------------------------
-- Conversion between homogeneous and heterogeneously indexed relations

module _ {i a b} {I : Set i} {A : I → Set a} {B : I → Set b} where

  OverPath : ∀ {ℓ} → IREL A B ℓ → ∀ {i j} → i ≡ j → REL (A i) (B j) ℓ
  OverPath _∼_ refl = _∼_

  toHetIndexed : ∀ {ℓ} → IREL A B ℓ → I.IREL A B (i ⊔ ℓ)
  toHetIndexed _∼_ {i} {j} x y = (p : i ≡ j) → OverPath _∼_ p x y

  fromHetIndexed : ∀ {ℓ} → I.IREL A B ℓ → IREL A B ℓ
  fromHetIndexed _∼_ = _∼_

------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" in multiple Setoids.
------------------------------------------------------------------------

-- Example use:
--
--   open import Data.Maybe.Properties
--   open import Data.Maybe.Relation.Binary.Equality
--   open import Relation.Binary.Reasoning.MultiSetoid
--
--   begin⟨ S ⟩
--     x ≈⟨ drop-just (begin⟨ setoid S ⟩
--          just x ≈⟨ justx≈mz ⟩
--          mz     ≈⟨ mz≈justy ⟩
--          just y ∎)⟩
--     y ≈⟨ y≈z ⟩
--     z ∎

-- Note this module is not reimplemented in terms of `Reasoning.Setoid`
-- as this introduces unsolved metas as the underlying base module
-- `Base.Single` does not require `_≈_` be symmetric.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Reasoning.MultiSetoid where

open import Function.Base using (flip)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

import Relation.Binary.Reasoning.Setoid as EqR

------------------------------------------------------------------------
-- Combinators that take the current setoid as an explicit argument.

module _ {c ℓ} (S : Setoid c ℓ) where
  open Setoid S

  data IsRelatedTo (x y : _) : Set (c ⊔ ℓ) where
    relTo : (x∼y : x ≈ y) → IsRelatedTo x y

  infix 1 begin⟨_⟩_

  begin⟨_⟩_ : ∀ {x y} → IsRelatedTo x y → x ≈ y
  begin⟨_⟩_ (relTo eq) = eq

------------------------------------------------------------------------
-- Combinators that take the current setoid as an implicit argument.

module _ {c ℓ} {S : Setoid c ℓ} where

  open Setoid S renaming (_≈_ to _≈_)

  infixr 2 step-≈ step-≈˘ step-≡ step-≡˘ _≡⟨⟩_
  infix 3 _∎

  step-≈ : ∀ x {y z} → IsRelatedTo S y z → x ≈ y → IsRelatedTo S x z
  step-≈ x (relTo y∼z) x∼y = relTo (trans x∼y y∼z)

  step-≈˘ : ∀ x {y z} → IsRelatedTo S y z → y ≈ x → IsRelatedTo S x z
  step-≈˘ x y∼z x≈y = step-≈ x y∼z (sym x≈y)

  step-≡ : ∀ x {y z} → IsRelatedTo S y z → x ≡ y → IsRelatedTo S x z
  step-≡ _ x∼z P.refl = x∼z

  step-≡˘ : ∀ x {y z} → IsRelatedTo S y z → y ≡ x → IsRelatedTo S x z
  step-≡˘ _ x∼z P.refl = x∼z

  _≡⟨⟩_ : ∀ x {y} → IsRelatedTo S x y → IsRelatedTo S x y
  _ ≡⟨⟩ x∼y = x∼y

  _∎ : ∀ x → IsRelatedTo S x x
  _∎ _ = relTo refl

  syntax step-≈  x y∼z x≈y = x ≈⟨  x≈y ⟩ y∼z
  syntax step-≈˘ x y∼z y≈x = x ≈˘⟨ y≈x ⟩ y∼z
  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

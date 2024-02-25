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

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Reasoning.MultiSetoid where

open import Level using (Level; _⊔_)
open import Function.Base using (case_of_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions using (Trans; Reflexive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax

private
  variable
    a ℓ : Level

------------------------------------------------------------------------
-- Combinators that take the current setoid as an explicit argument.

module _ (S : Setoid a ℓ) where
  open Setoid S

  data IsRelatedTo (x y : _) : Set (a ⊔ ℓ) where
    relTo : (x≈y : x ≈ y) → IsRelatedTo x y

  start : IsRelatedTo ⇒ _≈_
  start (relTo x≈y) = x≈y

  ≡-go : Trans _≡_ IsRelatedTo IsRelatedTo
  ≡-go x≡y (relTo y∼z) = relTo (case x≡y of λ where ≡.refl → y∼z)

  ≈-go : Trans _≈_ IsRelatedTo IsRelatedTo
  ≈-go x≈y (relTo y≈z) = relTo (trans x≈y y≈z)

  end : Reflexive IsRelatedTo
  end = relTo refl

------------------------------------------------------------------------
-- Reasoning combinators

-- Those that take the current setoid as an explicit argument.
  open begin-syntax IsRelatedTo start public
    renaming (begin_ to begin⟨_⟩_)


-- Those that take the current setoid as an implicit argument.
module _ {S : Setoid a ℓ} where
  open Setoid S

  open ≡-syntax (IsRelatedTo S) (≡-go S)
  open ≈-syntax (IsRelatedTo S) (IsRelatedTo S) (≈-go S) sym public
  open end-syntax (IsRelatedTo S) (end S) public

------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Morphism.Construct.Identity where

open import Data.Product.Base using (_,_)
open import Function.Base using (id)
import Function.Construct.Identity as Id
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid; Preorder; Poset)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism; IsRelIsomorphism
        ; IsOrderHomomorphism; IsOrderMonomorphism; IsOrderIsomorphism)
open import Relation.Binary.Morphism.Bundles
  using (SetoidHomomorphism; SetoidMonomorphism; SetoidIsomorphism
        ; PreorderHomomorphism; PosetHomomorphism)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------
-- Structures

module _ (≈ : Rel A ℓ₁) where

  isRelHomomorphism : IsRelHomomorphism ≈ ≈ id
  isRelHomomorphism = record
    { cong = Id.congruent ≈
    }

  isRelMonomorphism : IsRelMonomorphism ≈ ≈ id
  isRelMonomorphism = record
    { isHomomorphism = isRelHomomorphism
    ; injective      = Id.injective ≈
    }

  isRelIsomorphism : Reflexive ≈ → IsRelIsomorphism ≈ ≈ id
  isRelIsomorphism refl = record
    { isMonomorphism = isRelMonomorphism
    ; surjective     = Id.surjective ≈
    }

------------------------------------------------------------------------
-- Bundles

module _ (S : Setoid a ℓ₁) where

  open Setoid S

  setoidHomomorphism : SetoidHomomorphism S S
  setoidHomomorphism = record { isRelHomomorphism = isRelHomomorphism _≈_ }

  setoidMonomorphism : SetoidMonomorphism S S
  setoidMonomorphism = record { isRelMonomorphism = isRelMonomorphism _≈_ }

  setoidIsomorphism : SetoidIsomorphism S S
  setoidIsomorphism = record { isRelIsomorphism = isRelIsomorphism _ refl }

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------
-- Structures

module _ (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) where

  isOrderHomomorphism : IsOrderHomomorphism ≈ ≈ ∼ ∼ id
  isOrderHomomorphism = record
    { cong = id
    ; mono = id
    }

  isOrderMonomorphism : IsOrderMonomorphism ≈ ≈ ∼ ∼ id
  isOrderMonomorphism = record
    { isOrderHomomorphism = isOrderHomomorphism
    ; injective           = Id.injective ≈
    ; cancel              = id
    }

  isOrderIsomorphism : Reflexive ≈ → IsOrderIsomorphism ≈ ≈ ∼ ∼ id
  isOrderIsomorphism refl = record
    { isOrderMonomorphism = isOrderMonomorphism
    ; surjective          = Id.surjective ≈
    }

------------------------------------------------------------------------
-- Bundles

module _ (P : Preorder a ℓ₁ ℓ₂) where

  preorderHomomorphism : PreorderHomomorphism P P
  preorderHomomorphism = record { isOrderHomomorphism = isOrderHomomorphism _ _ }

module _ (P : Poset a ℓ₁ ℓ₂) where

  posetHomomorphism : PosetHomomorphism P P
  posetHomomorphism = record { isOrderHomomorphism = isOrderHomomorphism _ _ }

------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product using (_,_)
open import Function.Base using (id)
open import Relation.Binary
open import Relation.Binary.Morphism.Structures

module Relation.Binary.Morphism.Construct.Identity
  {a ℓ} {A : Set a} (≈ : Rel A ℓ) where

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

isRelHomomorphism : IsRelHomomorphism ≈ ≈ id
isRelHomomorphism = record
  { cong = id
  }

isRelMonomorphism : IsRelMonomorphism ≈ ≈ id
isRelMonomorphism = record
  { isHomomorphism = isRelHomomorphism
  ; injective      = id
  }

isRelIsomorphism : Reflexive ≈ → IsRelIsomorphism ≈ ≈ id
isRelIsomorphism refl = record
  { isMonomorphism = isRelMonomorphism
  ; surjective     = λ y → y , refl
  }

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

module _ {ℓ₂} (∼ : Rel A ℓ₂) where

  isOrderHomomorphism : IsOrderHomomorphism ≈ ≈ ∼ ∼ id
  isOrderHomomorphism = record
    { cong = id
    ; mono = id
    }

  isOrderMonomorphism : IsOrderMonomorphism ≈ ≈ ∼ ∼ id
  isOrderMonomorphism = record
    { isOrderHomomorphism = isOrderHomomorphism
    ; injective           = id
    ; cancel              = id
    }

  isOrderIsomorphism : Reflexive ≈ → IsOrderIsomorphism ≈ ≈ ∼ ∼ id
  isOrderIsomorphism refl = record
    { isOrderMonomorphism = isOrderMonomorphism
    ; surjective          = λ y → y , refl
    }

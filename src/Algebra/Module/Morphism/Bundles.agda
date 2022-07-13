------------------------------------------------------------------------
-- The Agda standard library
--
-- Useful bundles involving morphisms between module-like structures.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Bundles where

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Algebra.Module.Morphism.Structures
open import Function
open import Level                     using (Level; suc; _⊔_)
open import Relation.Binary
import Relation.Binary.ExtensionalEquivalence as ExtEq

module _
  {r ℓr m ℓm n ℓn : Level}
  {ring           : CommutativeRing r ℓr}
  (modA           : Module ring m ℓm)
  (modB           : Module ring n ℓn)
  where

  open Module modA renaming (Carrierᴹ to A)
  open Module modB renaming (Carrierᴹ to B)

  record LinearMap : Set (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ n ⊔ ℓn) where

    constructor mkLM

    field
      f    : A → B
      homo : IsModuleHomomorphism modA modB f
    open IsModuleHomomorphism homo public

  ≈ᴸ-setoid : Setoid (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ n ⊔ ℓn) (m ⊔ ℓn)
  ≈ᴸ-setoid = record
    { Carrier       = LinearMap
    ; _≈_           = _≗_ on LinearMap.f
    ; isEquivalence = record
        { refl  = ≗-refl
        ; sym   = ≗-sym
        ; trans = ≗-trans
        }
    }
    where open ExtEq (Module.≈ᴹ-setoid modB)

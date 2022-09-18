------------------------------------------------------------------------
-- The Agda standard library
--
-- Some bundles of linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Bundles where

open import Algebra                             using (CommutativeRing; Field)
open import Algebra.Linear.Structures
open import Algebra.Module                      using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
open import Data.List
open import Level                               using (Level; _⊔_; suc)
open import Relation.Binary

record DotProductSpace r ℓr m ℓm : Set (suc (r ⊔ ℓr ⊔ m ⊔ ℓm)) where

  field
    fld               : Field r ℓr
    mod               : Module (Field.ring fld) m ℓm
    toList            : Module.Carrierᴹ mod →
                        List (CommutativeRing.Carrier (Field.ring fld))
    isDotProductSpace : IsDotProductSpace fld mod toList

  open IsDotProductSpace isDotProductSpace public

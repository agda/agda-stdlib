------------------------------------------------------------------------
-- The Agda standard library
--
-- The binary relation defined by a constant
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Constant where

open import Level
open import Relation.Binary

private
  variable
    a b c : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Re-export definition

open import Relation.Binary.Construct.Constant.Core public

------------------------------------------------------------------------
-- Properties

module _ {a c} (A : Set a) {C : Set c} where

  refl : C → Reflexive {A = A} (Const C)
  refl c = c

  sym : Symmetric {A = A} (Const C)
  sym c = c

  trans : Transitive {A = A} (Const C)
  trans c d = c

  isEquivalence : C → IsEquivalence {A = A} (Const C)
  isEquivalence c = record
    { refl  = λ {x} → refl c {x}
    ; sym   = λ {x} {y} → sym {x} {y}
    ; trans = λ {x} {y} {z} → trans {x} {y} {z}
    }

  setoid : C → Setoid a c
  setoid x = record { isEquivalence = isEquivalence x }

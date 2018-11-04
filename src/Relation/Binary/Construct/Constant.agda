------------------------------------------------------------------------
-- The Agda standard library
--
-- The binary relation defined by a constant
------------------------------------------------------------------------

module Relation.Binary.Construct.Constant where

open import Relation.Binary

------------------------------------------------------------------------
-- Definition

Const : ∀ {a b c} {A : Set a} {B : Set b} → Set c → REL A B c
Const I = λ _ _ → I

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

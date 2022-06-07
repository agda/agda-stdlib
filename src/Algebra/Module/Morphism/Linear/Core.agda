------------------------------------------------------------------------
-- The Agda standard library
--
-- Linear maps between modules with the same underlying ring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                   using (CommutativeRing)
open import Algebra.Module            using (Module)
open import Level                     using (Level; suc; _⊔_)

module Algebra.Module.Morphism.Linear.Core
  {r ℓr m ℓm n ℓn : Level}
  {ring           : CommutativeRing r ℓr}
  (modA           : Module ring m ℓm)
  (modB           : Module ring n ℓn)
  where

open import Algebra.Module.Morphism.Structures
open import Function
open import Relation.Binary

module A = Module modA
open A renaming (Carrierᴹ to A)
module B = Module modB
open B renaming (Carrierᴹ to B)
  
record LinMap : Set (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ n ⊔ ℓn) where

  constructor mkLM
  field
    f    : A → B
    homo : IsModuleHomomorphism modA modB f
  open IsModuleHomomorphism homo public
  
  infix 4 _≗_

  _≗_ : (f g : A → B) → Set (ℓn ⊔ m)
  (f ≗ g) = ∀ x → f x B.≈ᴹ g x

  ≗-refl : Reflexive _≗_
  ≗-refl x = Setoid.refl B.≈ᴹ-setoid

  ≗-sym : Symmetric _≗_
  ≗-sym f≗g x = Setoid.sym B.≈ᴹ-setoid (f≗g x)

  ≗-trans : Transitive _≗_
  ≗-trans f≗g g≗h x = Setoid.trans B.≈ᴹ-setoid (f≗g x) (g≗h x)

≈ᴸ-setoid : LinMap → Setoid (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ n ⊔ ℓn) (m ⊔ ℓn)
≈ᴸ-setoid lm = record
  { Carrier = LinMap
  ; _≈_     = (LinMap._≗_ lm) on (LinMap.f)
  ; isEquivalence = record
      { refl  = LinMap.≗-refl lm
      ; sym   = LinMap.≗-sym lm
      ; trans = LinMap.≗-trans lm
      }
  }


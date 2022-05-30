------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstract vector spaces.
--
-- A "vector space" is a Module with a commutative, homomorphic inner
-- product and a complete set of building blocks for mapping the space.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.VectorSpace.Core where

import Algebra.Module.Morphism.Structures    as MorphismStructures

open import Algebra        using (CommutativeRing)
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Data.List      using (List; foldl; foldr)
open import Data.Product
open import Function
open import Level          using (Level; _⊔_; suc)
open import Relation.Binary --                    hiding (_⇔_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

module _
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  where

  open CommutativeRing ring renaming (Carrier  to S)  -- "S" for scalar.
  open Module          mod  renaming (Carrierᴹ to V)  -- "V" for vector.
  open MorphismStructures.ModuleMorphisms mod ⟨module⟩

  record VectorSpace : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where

    constructor mkVS
    infix 7 _∙_
    field
      _∙_           : V → V → S
      basisSet      : List V
      basisComplete : ∀ {a : V} →
                      a ≈ᴹ foldr ( _+ᴹ_
                                 ∘ (uncurry _*ₗ_)
                                 ∘ < (a ∙_) , id >
                                 ) 0ᴹ basisSet
      -- ToDo: Can these be unified, by using one of the
      -- existing algebraic structures?
      -- I'm only finding things that are predicated upon: `A → A → A`, or
      -- `A → B`; nothing for: `A → A → B`.
      ∙-comm        : ∀ {a b : V} → a ∙ b ≈ b ∙ a
      ∙-distrib-+   : ∀ {a b c : V} → a ∙ (b +ᴹ c) ≈ (a ∙ b) + (a ∙ c)
      ∙-comm-*ₗ     : ∀ {s : S} {a b : V} → a ∙ (s *ₗ b) ≈ s * (a ∙ b)
      ∙-congˡ       : ∀ {a b c} → b ≈ᴹ c → a ∙ b ≈ a ∙ c
      ∙-congʳ       : ∀ {a b c} → b ≈ᴹ c → b ∙ a ≈ c ∙ a  -- Prove.
      ∙-idˡ         : ∀ {a : V} → 0ᴹ ∙ a ≈ 0#
      ∙-idʳ         : ∀ {a : V} → a ∙ 0ᴹ ≈ 0#              -- Prove.

  ------------------------------------------------------------------------
  -- Pointwise equivalence over the underlying scalar field.
  -- (Copied from `Relation.Binary.PropositionalEquality` and modified.)
  infix 4 _≗_

  -- Note: `x` is kept explicit, to allow `C-c C-c` on list args, in:
  --       `Properties`, etc.
  -- _≗_ : (f g : A → S) → Set _  -- Caused level solving errors.
  _≗_ : (f g : V → S) → Set (ℓr ⊔ m)
  f ≗ g = ∀ x → f x ≈ g x

  ≗-refl : Reflexive _≗_
  ≗-refl x = Setoid.refl setoid

  ≗-sym : Symmetric _≗_
  ≗-sym f≗g x = Setoid.sym setoid (f≗g x)

  ≗-trans : Transitive _≗_
  ≗-trans f≗g g≗h x = Setoid.trans setoid (f≗g x) (g≗h x)

  ------------------------------------------------------------------------
  -- Linear maps from vectors to scalars.
  record LinMap : Set (m ⊔ r ⊔ ℓr ⊔ ℓm) where
    constructor mkLM
    field
      f    : V → S
      homo : IsModuleHomomorphism f

  lm-setoid : Setoid _ _
  lm-setoid = record
    { Carrier = LinMap
    ; _≈_     = _≗_ on LinMap.f
    ; isEquivalence = record
        { refl  = ≗-refl
        ; sym   = ≗-sym
        ; trans = ≗-trans
        }
    }

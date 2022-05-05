------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Linear.Core where

import Function.Definitions
import Relation.Binary.Reasoning.Setoid

open import Algebra          using (CommutativeRing)
open import Algebra.Module   using (Module)
open import Level            using (Level; _⊔_; suc)
open import Relation.Binary  using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)
open import Relation.Nullary using (¬_)

module _
  {r ℓr m ℓm : Level}
  {ring : CommutativeRing r ℓr}
  (modA : Module ring m ℓm)
  (modB : Module ring m ℓm)
  where

  lm = suc (ℓm ⊔ m ⊔ r)
  record LinMap : Set lm where

    constructor mkLM
    open Module modA public
      using () renaming
      ( Carrierᴹ  to A
      ; _+ᴹ_      to _+ᴬ_
      ; _*ₗ_      to _·ᴬ_
      ; _≈ᴹ_      to _≈ᴬ_
      ; 0ᴹ        to 0ᴬ
      ; ≈ᴹ-setoid to ≈ᴬ-setoid
      ; *ₗ-zeroˡ  to ·ᴬ-zeroˡ
      ; ≈ᴹ-sym    to symᴬ
      ; non-zeroʳ to non-zeroʳᴬ
      ; non-zeroˡ to non-zeroˡᴬ
      )
    open Module modB public
      using () renaming
      ( Carrierᴹ  to B
      ; _+ᴹ_      to _+ᴮ_
      ; _*ₗ_      to _·ᴮ_
      ; _≈ᴹ_      to _≈ᴮ_
      ; 0ᴹ        to 0ᴮ
      ; ≈ᴹ-setoid to ≈ᴮ-setoid
      ; *ₗ-zeroˡ  to ·ᴮ-zeroˡ
      ; ≈ᴹ-sym    to symᴮ
      ; non-zeroʳ to non-zeroʳᴮ
      ; non-zeroˡ to non-zeroˡᴮ
      )
    open CommutativeRing ring public
      using () renaming
      ( Carrier to S
      ; 0#      to 𝟘
      )
    -- open Relation.Binary.Setoid           ≈ᴬ-setoid public
    --   using () renaming (_≈_ to _≈ᴬ_)
    -- open Relation.Binary.Setoid           ≈ᴮ-setoid public
    --   using (_≈_)
    open Relation.Binary.Reasoning.Setoid ≈ᴮ-setoid public
    open Function.Definitions _≈ᴬ_ _≈ᴮ_
    field
      f      : A → B
      adds   : ∀ {a₁ a₂ : A}      → f (a₁ +ᴬ a₂) ≈ᴮ f a₁ +ᴮ f a₂
      scales : ∀ {s : S} {a : A} → f (s ·ᴬ  a) ≈ᴮ s    ·ᴮ f a
      f-cong : Congruent f

    _≉ᴬ_ : A → A → Set ℓm
    x ≉ᴬ y = ¬ (x ≈ᴬ y)

    _≉ᴮ_ : B → B → Set ℓm
    x ≉ᴮ y = ¬ (x ≈ᴮ y)

    _≈ᴸᴹ_ : Rel LinMap m
    lm₁ ≈ᴸᴹ lm₂ = f ≡ f

    isEquivalence : IsEquivalence _≈ᴸᴹ_
    isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }

    open IsEquivalence isEquivalence public

    ≈ᴸᴹ-setoid : Setoid lm m
    ≈ᴸᴹ-setoid = record { isEquivalence = isEquivalence }
  -- open LinMap public

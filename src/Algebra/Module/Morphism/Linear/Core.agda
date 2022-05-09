------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for linear maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Morphism.Linear.Core where

import Algebra.Module.Properties as Properties
import Function.Definitions
import Relation.Binary.Reasoning.Setoid as Reasoning

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
      ( Carrierᴹ       to A
      ; _+ᴹ_           to _+ᴬ_
      ; _*ₗ_           to _·ᴬ_
      ; -ᴹ_            to -ᴬ_
      ; _≈ᴹ_           to _≈ᴬ_
      ; 0ᴹ             to 0ᴬ
      ; +ᴹ-comm        to +ᴬ-comm
      ; +ᴹ-congˡ       to +ᴬ-congˡ
      ; +ᴹ-congʳ       to +ᴬ-congʳ
      ; *ₗ-zeroˡ       to ·ᴬ-zeroˡ
      ; -ᴹ‿cong        to -ᴬ‿cong
      ; -ᴹ‿inverseʳ    to -ᴬ‿inverseʳ
      ; uniqueʳ‿-ᴹ     to uniqueʳ‿-ᴬ
      ; ≈ᴹ-setoid      to ≈ᴬ-setoid
      ; ≈ᴹ-sym         to symᴬ
      ; leftSemimodule to leftSemimoduleᴬ
      )
    open Properties leftSemimoduleᴬ public
      using () renaming
      ( non-zeroʳ to non-zeroʳᴬ
      ; non-zeroˡ to non-zeroˡᴬ
      )

    open Module modB public
      using () renaming
      ( Carrierᴹ       to B
      ; _+ᴹ_           to _+ᴮ_
      ; _*ₗ_           to _·ᴮ_
      ; -ᴹ_            to -ᴮ_
      ; _≈ᴹ_           to _≈ᴮ_
      ; 0ᴹ             to 0ᴮ
      ; +ᴹ-comm        to +ᴮ-comm
      ; +ᴹ-congˡ       to +ᴮ-congˡ
      ; +ᴹ-congʳ       to +ᴮ-congʳ
      ; *ₗ-zeroˡ       to ·ᴮ-zeroˡ
      ; -ᴹ‿cong        to -ᴮ‿cong
      ; -ᴹ‿inverseʳ    to -ᴮ‿inverseʳ
      ; uniqueʳ‿-ᴹ     to uniqueʳ‿-ᴮ
      ; ≈ᴹ-setoid      to ≈ᴮ-setoid
      ; ≈ᴹ-sym         to symᴮ
      ; leftSemimodule to leftSemimoduleᴮ
      )
    open Properties leftSemimoduleᴮ public
      using () renaming
      ( non-zeroʳ to non-zeroʳᴮ
      ; non-zeroˡ to non-zeroˡᴮ
      )

    open CommutativeRing ring public
      using (_*_) renaming
      ( Carrier to S
      ; 0#      to 𝟘
      ; 1#      to 𝟙
      )
    open module Reasoningᴬ = Reasoning ≈ᴬ-setoid public
      using () renaming
      ( begin_ to beginᴬ_
      ; _∎     to _∎ᴬ
      )
    infixr 2 step-≈ᴬ
    step-≈ᴬ = Reasoningᴬ.step-≈
    syntax step-≈ᴬ x y≈z x≈y = x ≈ᴬ⟨ x≈y ⟩ y≈z
    open module Reasoningᴮ = Reasoning ≈ᴮ-setoid public
    open Function.Definitions _≈ᴬ_ _≈ᴮ_

    field
      f      : A → B
      adds   : ∀ {a₁ a₂ : A}      → f (a₁ +ᴬ a₂) ≈ᴮ f a₁ +ᴮ f a₂
      scales : ∀ {s : S} {a : A} → f (s ·ᴬ  a) ≈ᴮ s    ·ᴮ f a
      f-cong : Congruent f
      ¬-involutive-≈ᴬ : {a₁ a₂ : A} → ¬ (¬ (a₁ ≈ᴬ a₂)) → a₁ ≈ᴬ a₂
      ¬-involutive-≈ᴮ : {b₁ b₂ : B} → ¬ (¬ (b₁ ≈ᴮ b₂)) → b₁ ≈ᴮ b₂
      -ᴬ‿involutive   : {a : A} → -ᴬ (-ᴬ a) ≈ᴬ a
      -ᴮ‿involutive   : {b : B} → -ᴮ (-ᴮ b) ≈ᴮ b
      
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

------------------------------------------------------------------------
-- The Agda standard library
--
-- Function Equality setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Relation.Binary.Equality where

  open import Function.Bundles using (Func; _⟨$⟩_)
  open import Level using (Level)
  open import Relation.Binary.Bundles using (Setoid)

  private
    variable
      a₁ a₂ b₁ b₂ c₁ c₂ : Level
      
  setoid : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  setoid From To = record
    { Carrier = Func From To
    ; _≈_ = λ f g → ∀ {x} → f ⟨$⟩ x To.≈ g ⟨$⟩ x
    ; isEquivalence = record
      { refl = To.refl
      ; sym = λ f≈g → To.sym f≈g
      ; trans = λ f≈g g≈h → To.trans f≈g g≈h
      }
    }
    where
      module To = Setoid To

  -- most of the time, this infix version is nicer to use
  infixr 9 _⇨_
  _⇨_ : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  _⇨_ = setoid

------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstract vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.VectorSpace.Core where

import Relation.Binary.Reasoning.Setoid as Reasoning

open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Linear      using (LinMap)
open import Data.List                           using (List; foldl)
open import Level                               using (Level; _⊔_; suc)

module _
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  {mod       : Module ring r ℓr}
  (lm        : LinMap mod ⟨module⟩)
  where

  vs = suc (ℓr ⊔ ℓm ⊔ m ⊔ r)
  record VectorSpace : Set vs where

    constructor mkVS

    open LinMap lm public
      using (S; _*_; f; begin_; _∎; sym) renaming
      ( A    to T
      ; _+ᴬ_ to _+ᵀ_
      ; _·ᴬ_ to _·_
      ; _≈ᴬ_ to _≈ᵀ_
      ; 0ᴬ   to 0ᵀ
      ; _+ᴮ_ to _+_
      ; _≈ᴮ_ to _≈_
      ; _≉ᴮ_ to _≉_
      ; 0ᴮ   to 𝟘
      )
    infixr 2 step-≈
    step-≈ = LinMap.step-≈
    syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
    
    infix 7 _∘_
    field
      basisSet    : List T
      _∘_         : T → T → S
      comm-∘      : ∀ {a b : T} → a ∘ b ≈ b ∘ a
      ∘-distrib-+ : ∀ {a b c : T} → a ∘ (b +ᵀ c) ≈ (a ∘ b) + (a ∘ c)
      ∘-comm-·    : ∀ {s : S} {a b : T} → a ∘ (s · b) ≈ s * (a ∘ b)
      orthonormal : ∀ {x : T} →
                    ( foldl (λ acc v → acc +ᵀ (f v) · v)
                            0ᵀ basisSet
                    ) ∘ x ≈ f x


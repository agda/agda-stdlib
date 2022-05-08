------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstract vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.VectorSpace.Core where

import Relation.Binary.Reasoning.Setoid as Reasoning

open import Algebra          using (CommutativeRing)
open import Algebra.Module   using (Module)
open import Data.List        using (List; foldl)
open import Level            using (Level; _⊔_; suc)

module _
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  where

  vs = suc (ℓr ⊔ ℓm ⊔ m ⊔ r)
  record VectorSpace : Set vs where

    constructor mkVS

    open Module mod public
      using () renaming
      ( Carrierᴹ  to T
      ; _+ᴹ_      to _+ᵀ_
      ; _*ₗ_      to _·_
      ; _≈ᴹ_      to _≈ᵀ_
      ; ≈ᴹ-setoid to ≈-setoid
      ; 0ᴹ        to 𝟘
      )

    open CommutativeRing ring public
      using () renaming
      ( Carrier to A
      ; _+_     to _+ᴬ_
      ; _*_     to _*ᴬ_
      ; _≈_     to _≈ᴬ_
      )

    open Reasoning ≈-setoid public

    infix 7 _∘_
    field
      basisSet    : List T
      _∘_         : T → T → A
      comm-∘      : ∀ {a b : T} → a ∘ b ≈ᴬ b ∘ a
      ∘-distrib-+ : ∀ {a b c : T} → a ∘ (b +ᵀ c) ≈ᴬ (a ∘ b) +ᴬ (a ∘ c)
      ∘-comm-·    : ∀ {s : A} {a b : T} → a ∘ (s · b) ≈ᴬ s *ᴬ (a ∘ b)
      orthonormal : ∀ {f : T → A} → {x : T} →
                    ( foldl (λ acc v → acc +ᵀ (f v) · v)
                            𝟘 basisSet
                    ) ∘ x ≈ᴬ f x

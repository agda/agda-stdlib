------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Data.VectorSpace.Core               using (VectorSpace)
open import Level                               using (Level; _⊔_; suc)

module Data.VectorSpace.Properties
  {r ℓr : Level}
  {ring : CommutativeRing r ℓr}
  {mod  : Module ring r ℓr}
  (vs   : VectorSpace mod)
  where

-- import Relation.Binary.Reasoning.Setoid          as Reasoning
import Algebra.Module.Morphism.Structures        as MorphismStructures
-- import Algebra.Module.Properties                 as ModProps

open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Linear.Properties mod ⟨module⟩
open import Data.List                           using (foldl)
open import Data.Product
  using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)

open CommutativeRing ring
  using (_+_; _*_; _≈_) renaming
  ( Carrier to S
  )
open Module mod
  using () renaming
  ( Carrierᴹ       to T
  ; _+ᴹ_           to _+ᵀ_
  ; _*ₗ_           to _·_
  ; -ᴹ_            to -ᵀ_
  ; _≈ᴹ_           to _≈ᵀ_
  ; 0ᴹ             to 0ᵀ
  ; +ᴹ-comm        to +ᵀ-comm
  ; +ᴹ-congˡ       to +ᵀ-congˡ
  ; +ᴹ-congʳ       to +ᵀ-congʳ
  ; *ₗ-zeroˡ       to ·ᵀ-zeroˡ
  ; -ᴹ‿cong        to -ᵀ‿cong
  ; -ᴹ‿inverseʳ    to -ᵀ‿inverseʳ
  ; -ᴹ‿involutive  to -ᵀ‿involutive
  ; uniqueʳ‿-ᴹ     to uniqueʳ‿-ᵀ
  ; ≈ᴹ-setoid      to ≈ᵀ-setoid
  ; ≈ᴹ-sym         to symᵀ
  ; leftSemimodule to leftSemimoduleᵀ
  )
open MorphismStructures.ModuleMorphisms mod ⟨module⟩
open VectorSpace vs

-- properties predicated upon a linear map from tensor to scalar
module _
  {⟦_⟧ : T → S}
  (isModuleHomomorphism : IsModuleHomomorphism ⟦_⟧)
  where

  open IsModuleHomomorphism isModuleHomomorphism

  -- basisSet = {b₀, b₁}
  -- orthonormal :
  --   (0 + f b₀ · b₀ + f b₁ · b₁) ∘ a ≈ f a        ≈⟨ ∘-distrib-+ ⟩
  --   f a ≈ a ∘ (f b₀ · b₀) + a ∘ (f b₁ · b₁)      ≈⟨ ∘-comm-· ⟩
  --   f a ≈ f b₀ * (a ∘ b₀) + f b₁ * (a ∘ b₁)      ≈⟨ f linear ⟩
  --   f a ≈ f ((a ∘ b₀) · b₀) + f ((a ∘ b₁) · b₁)  ≈⟨ f linear ⟩
  --   f a ≈ f ((a ∘ b₀) · b₀ + (a ∘ b₁) · b₁)      ≈⟨ subst ⟩
  --   a ≈ (a ∘ b₀) · b₀ + (a ∘ b₁) · b₁            ≈⟨ generalize ⟩
  --   a ≈ foldl (λ acc b → acc + (a ∘ b)·b) 0 basisSet

  T⊸S≈b∘ : ∀ {a : T} {s : S} {f : T → S} {_ : IsModuleHomomorphism f} →
           ( foldl (λ acc b → acc +ᵀ (f b) · b)
                   0ᵀ basisSet
           ) ∘ a ≈ f a
  T⊸S≈b∘ = {!!}

  -- x·z≈y·z→x≈y : {x y : T} → Σ[ y ∈ T ] f y ≉ 𝟘 →
  --   (∀ {z : T} → x ∘ z ≈ y ∘ z) → x ≈ᵀ y
  -- x·z≈y·z→x≈y {x = x} {y = y} Σ[y]fy≉𝟘 x∘z≈y∘z =
  --   let z = foldl (λ acc v → acc +ᵀ f v · v) 0ᵀ basisSet
  --       -- x·z≈y·z = x∘z≈y∘z {z}
  --       z·x≈y·z : z ∘ x ≈ y ∘ z
  --       -- z·x≈y·z = step-≈ (z ∘ x) x·z≈y·z comm-∘
  --       -- z·x≈y·z = step-≈ (z ∘ x) x∘z≈y∘z {z} comm-∘
  --       z·x≈y·z = begin (z ∘ x) ≈⟨ comm-∘ ⟩ x∘z≈y∘z {z} ∎
  --       z·x≈z·y : z ∘ x ≈ z ∘ y
  --       z·x≈z·y = sym (step-≈ (z ∘ y) (sym z·x≈y·z) comm-∘)
  --       fx≈z·y : f x ≈ z ∘ y
  --       fx≈z·y = step-≈ (f x) z·x≈z·y (sym orthonormal)
  --       fx≈fy : f x ≈ f y
  --       fx≈fy = sym (step-≈ (f y) (sym fx≈z·y) (sym orthonormal))
  --    in inj-lm Σ[y]fy≉𝟘 fx≈fy

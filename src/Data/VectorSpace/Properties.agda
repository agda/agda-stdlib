------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector spaces.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                             using (CommutativeRing)
open import Algebra.Module                      using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Linear      using (LinMap)
open import Data.VectorSpace.Core               using (VectorSpace)
open import Level                               using (Level; _⊔_; suc)

module Data.VectorSpace.Properties
  {r ℓr m ℓm : Level}
  {ring : CommutativeRing r ℓr}
  {mod : Module ring r ℓr}
  -- {mod  : Module ring m ℓm}
  {lm   : LinMap mod ⟨module⟩}
  (vs   : VectorSpace lm)
  where

open import Algebra.Module.Morphism.Linear using (LinMap; inj-lm)
open import Data.List                      using (foldl)
open import Data.Product
  using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)

open VectorSpace vs

x·z≈y·z→x≈y : {x y : T} → Σ[ y ∈ T ] f y ≉ 𝟘 →
  (∀ {z : T} → x ∘ z ≈ y ∘ z) → x ≈ᵀ y
x·z≈y·z→x≈y {x = x} {y = y} Σ[y]fy≉𝟘 x∘z≈y∘z =
  let z = foldl (λ acc v → acc +ᵀ f v · v) 0ᵀ basisSet
      -- x·z≈y·z = x∘z≈y∘z {z}
      z·x≈y·z : z ∘ x ≈ y ∘ z
      -- z·x≈y·z = step-≈ (z ∘ x) x·z≈y·z comm-∘
      -- z·x≈y·z = step-≈ (z ∘ x) x∘z≈y∘z {z} comm-∘
      z·x≈y·z = begin (z ∘ x) ≈⟨ comm-∘ ⟩ x∘z≈y∘z {z} ∎
      z·x≈z·y : z ∘ x ≈ z ∘ y
      z·x≈z·y = sym (step-≈ (z ∘ y) (sym z·x≈y·z) comm-∘)
      fx≈z·y : f x ≈ z ∘ y
      fx≈z·y = step-≈ (f x) z·x≈z·y (sym orthonormal)
      fx≈fy : f x ≈ f y
      fx≈fy = sym (step-≈ (f y) (sym fx≈z·y) (sym orthonormal))
   in inj-lm Σ[y]fy≉𝟘 fx≈fy

------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Morphism.Construct.Composition where

open import Algebra.Bundles
open import Algebra.Morphism.Bundles
open import Algebra.Morphism.Structures
open import Function.Base using (_∘_)
import Function.Construct.Composition as Func
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Composition
open import Relation.Binary.Definitions using (Transitive)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level


------------------------------------------------------------------------
-- Magmas

module _ {M₁ : RawMagma a ℓ₁}
         {M₂ : RawMagma b ℓ₂}
         {M₃ : RawMagma c ℓ₃}
         (open RawMagma)
         (≈₃-trans : Transitive (_≈_ M₃))
         {f : Carrier M₁ → Carrier M₂}
         {g : Carrier M₂ → Carrier M₃}
         where

  isMagmaHomomorphism
    : IsMagmaHomomorphism M₁ M₂ f
    → IsMagmaHomomorphism M₂ M₃ g
    → IsMagmaHomomorphism M₁ M₃ (g ∘ f)
  isMagmaHomomorphism f-homo g-homo = record
    { isRelHomomorphism = isRelHomomorphism F.isRelHomomorphism G.isRelHomomorphism
    ; homo              = λ x y → ≈₃-trans (G.⟦⟧-cong (F.homo x y)) (G.homo (f x) (f y))
    } where module F = IsMagmaHomomorphism f-homo; module G = IsMagmaHomomorphism g-homo

  isMagmaMonomorphism
    : IsMagmaMonomorphism M₁ M₂ f
    → IsMagmaMonomorphism M₂ M₃ g
    → IsMagmaMonomorphism M₁ M₃ (g ∘ f)
  isMagmaMonomorphism f-mono g-mono = record
    { isMagmaHomomorphism = isMagmaHomomorphism F.isMagmaHomomorphism G.isMagmaHomomorphism
    ; injective           = F.injective ∘ G.injective
    } where module F = IsMagmaMonomorphism f-mono; module G = IsMagmaMonomorphism g-mono

  isMagmaIsomorphism
    : IsMagmaIsomorphism M₁ M₂ f
    → IsMagmaIsomorphism M₂ M₃ g
    → IsMagmaIsomorphism M₁ M₃ (g ∘ f)
  isMagmaIsomorphism f-iso g-iso = record
    { isMagmaMonomorphism = isMagmaMonomorphism F.isMagmaMonomorphism G.isMagmaMonomorphism
    ; surjective          = Func.surjective _ _ (_≈_ M₃) F.surjective G.surjective
    } where module F = IsMagmaIsomorphism f-iso; module G = IsMagmaIsomorphism g-iso


------------------------------------------------------------------------
-- Monoids

module _ {M₁ : RawMonoid a ℓ₁}
         {M₂ : RawMonoid b ℓ₂}
         {M₃ : RawMonoid c ℓ₃}
         (open RawMonoid)
         (≈₃-trans : Transitive (_≈_ M₃))
         {f : Carrier M₁ → Carrier M₂}
         {g : Carrier M₂ → Carrier M₃}
         where

  isMonoidHomomorphism
    : IsMonoidHomomorphism M₁ M₂ f
    → IsMonoidHomomorphism M₂ M₃ g
    → IsMonoidHomomorphism M₁ M₃ (g ∘ f)
  isMonoidHomomorphism f-homo g-homo = record
    { isMagmaHomomorphism = isMagmaHomomorphism ≈₃-trans F.isMagmaHomomorphism G.isMagmaHomomorphism
    ; ε-homo              = ≈₃-trans (G.⟦⟧-cong F.ε-homo) G.ε-homo
    } where module F = IsMonoidHomomorphism f-homo; module G = IsMonoidHomomorphism g-homo

  isMonoidMonomorphism
    : IsMonoidMonomorphism M₁ M₂ f
    → IsMonoidMonomorphism M₂ M₃ g
    → IsMonoidMonomorphism M₁ M₃ (g ∘ f)
  isMonoidMonomorphism f-mono g-mono = record
    { isMonoidHomomorphism = isMonoidHomomorphism F.isMonoidHomomorphism G.isMonoidHomomorphism
    ; injective            = F.injective ∘ G.injective
    } where module F = IsMonoidMonomorphism f-mono; module G = IsMonoidMonomorphism g-mono

  isMonoidIsomorphism
    : IsMonoidIsomorphism M₁ M₂ f
    → IsMonoidIsomorphism M₂ M₃ g
    → IsMonoidIsomorphism M₁ M₃ (g ∘ f)
  isMonoidIsomorphism f-iso g-iso = record
    { isMonoidMonomorphism = isMonoidMonomorphism F.isMonoidMonomorphism G.isMonoidMonomorphism
    ; surjective           = Func.surjective _ _(_≈_ M₃)  F.surjective G.surjective
    } where module F = IsMonoidIsomorphism f-iso; module G = IsMonoidIsomorphism g-iso


------------------------------------------------------------------------
-- Groups

module _ {G₁ : RawGroup a ℓ₁}
         {G₂ : RawGroup b ℓ₂}
         {G₃ : RawGroup c ℓ₃}
         (open RawGroup)
         (≈₃-trans : Transitive (_≈_ G₃))
         {f : Carrier G₁ → Carrier G₂}
         {g : Carrier G₂ → Carrier G₃}
         where


  isGroupHomomorphism
    : IsGroupHomomorphism G₁ G₂ f
    → IsGroupHomomorphism G₂ G₃ g
    → IsGroupHomomorphism G₁ G₃ (g ∘ f)
  isGroupHomomorphism f-homo g-homo = record
    { isMonoidHomomorphism = isMonoidHomomorphism ≈₃-trans F.isMonoidHomomorphism G.isMonoidHomomorphism
    ; ⁻¹-homo              = λ x → ≈₃-trans (G.⟦⟧-cong (F.⁻¹-homo x)) (G.⁻¹-homo (f x))
    } where module F = IsGroupHomomorphism f-homo; module G = IsGroupHomomorphism g-homo

  isGroupMonomorphism
    : IsGroupMonomorphism G₁ G₂ f
    → IsGroupMonomorphism G₂ G₃ g
    → IsGroupMonomorphism G₁ G₃ (g ∘ f)
  isGroupMonomorphism f-mono g-mono = record
    { isGroupHomomorphism = isGroupHomomorphism F.isGroupHomomorphism G.isGroupHomomorphism
    ; injective           = F.injective ∘ G.injective
    } where module F = IsGroupMonomorphism f-mono; module G = IsGroupMonomorphism g-mono

  isGroupIsomorphism
    : IsGroupIsomorphism G₁ G₂ f
    → IsGroupIsomorphism G₂ G₃ g
    → IsGroupIsomorphism G₁ G₃ (g ∘ f)
  isGroupIsomorphism f-iso g-iso = record
    { isGroupMonomorphism = isGroupMonomorphism F.isGroupMonomorphism G.isGroupMonomorphism
    ; surjective          = Func.surjective  _ _ (_≈_ G₃) F.surjective G.surjective
    } where module F = IsGroupIsomorphism f-iso; module G = IsGroupIsomorphism g-iso


------------------------------------------------------------------------
-- Near semirings

module _ {R₁ : RawNearSemiring a ℓ₁}
         {R₂ : RawNearSemiring b ℓ₂}
         {R₃ : RawNearSemiring c ℓ₃}
         (open RawNearSemiring)
         (≈₃-trans : Transitive (_≈_ R₃))
         {f : Carrier R₁ → Carrier R₂}
         {g : Carrier R₂ → Carrier R₃}
         where

  isNearSemiringHomomorphism
    : IsNearSemiringHomomorphism R₁ R₂ f
    → IsNearSemiringHomomorphism R₂ R₃ g
    → IsNearSemiringHomomorphism R₁ R₃ (g ∘ f)
  isNearSemiringHomomorphism f-homo g-homo = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism ≈₃-trans F.+-isMonoidHomomorphism G.+-isMonoidHomomorphism
    ; *-homo = λ x y → ≈₃-trans (G.⟦⟧-cong (F.*-homo x y)) (G.*-homo (f x) (f y))
    } where module F = IsNearSemiringHomomorphism f-homo; module G = IsNearSemiringHomomorphism g-homo

  isNearSemiringMonomorphism
    : IsNearSemiringMonomorphism R₁ R₂ f
    → IsNearSemiringMonomorphism R₂ R₃ g
    → IsNearSemiringMonomorphism R₁ R₃ (g ∘ f)
  isNearSemiringMonomorphism f-mono g-mono = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism F.isNearSemiringHomomorphism G.isNearSemiringHomomorphism
    ; injective                  = F.injective ∘ G.injective
    } where module F = IsNearSemiringMonomorphism f-mono; module G = IsNearSemiringMonomorphism g-mono

  isNearSemiringIsomorphism
    : IsNearSemiringIsomorphism R₁ R₂ f
    → IsNearSemiringIsomorphism R₂ R₃ g
    → IsNearSemiringIsomorphism R₁ R₃ (g ∘ f)
  isNearSemiringIsomorphism f-iso g-iso = record
    { isNearSemiringMonomorphism = isNearSemiringMonomorphism F.isNearSemiringMonomorphism G.isNearSemiringMonomorphism
    ; surjective                 = Func.surjective _ _ (_≈_ R₃) F.surjective G.surjective
    } where module F = IsNearSemiringIsomorphism f-iso; module G = IsNearSemiringIsomorphism g-iso


------------------------------------------------------------------------
-- Semirings

module _
  {R₁ : RawSemiring a ℓ₁}
  {R₂ : RawSemiring b ℓ₂}
  {R₃ : RawSemiring c ℓ₃}
  (open RawSemiring)
  (≈₃-trans : Transitive (_≈_ R₃))
  {f : Carrier R₁ → Carrier R₂}
  {g : Carrier R₂ → Carrier R₃}
  where


  isSemiringHomomorphism
    : IsSemiringHomomorphism R₁ R₂ f
    → IsSemiringHomomorphism R₂ R₃ g
    → IsSemiringHomomorphism R₁ R₃ (g ∘ f)
  isSemiringHomomorphism f-homo g-homo = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism ≈₃-trans F.isNearSemiringHomomorphism G.isNearSemiringHomomorphism
    ; 1#-homo                    = ≈₃-trans (G.⟦⟧-cong F.1#-homo) G.1#-homo
    } where module F = IsSemiringHomomorphism f-homo; module G = IsSemiringHomomorphism g-homo

  isSemiringMonomorphism
    : IsSemiringMonomorphism R₁ R₂ f
    → IsSemiringMonomorphism R₂ R₃ g
    → IsSemiringMonomorphism R₁ R₃ (g ∘ f)
  isSemiringMonomorphism f-mono g-mono = record
    { isSemiringHomomorphism = isSemiringHomomorphism F.isSemiringHomomorphism G.isSemiringHomomorphism
    ; injective              = F.injective ∘ G.injective
    } where module F = IsSemiringMonomorphism f-mono; module G = IsSemiringMonomorphism g-mono

  isSemiringIsomorphism
    : IsSemiringIsomorphism R₁ R₂ f
    → IsSemiringIsomorphism R₂ R₃ g
    → IsSemiringIsomorphism R₁ R₃ (g ∘ f)
  isSemiringIsomorphism f-iso g-iso = record
    { isSemiringMonomorphism = isSemiringMonomorphism F.isSemiringMonomorphism G.isSemiringMonomorphism
    ; surjective             = Func.surjective _ _ (_≈_ R₃) F.surjective G.surjective
    } where module F = IsSemiringIsomorphism f-iso; module G = IsSemiringIsomorphism g-iso

------------------------------------------------------------------------
-- RingWithoutOne

module _ {R₁ : RawRingWithoutOne a ℓ₁}
         {R₂ : RawRingWithoutOne b ℓ₂}
         {R₃ : RawRingWithoutOne c ℓ₃}
         (open RawRingWithoutOne)
         (≈₃-trans : Transitive (_≈_ R₃))
         {f : Carrier R₁ → Carrier R₂}
         {g : Carrier R₂ → Carrier R₃}
         where


  isRingWithoutOneHomomorphism
    : IsRingWithoutOneHomomorphism R₁ R₂ f
    → IsRingWithoutOneHomomorphism R₂ R₃ g
    → IsRingWithoutOneHomomorphism R₁ R₃ (g ∘ f)
  isRingWithoutOneHomomorphism f-homo g-homo = record
    { +-isGroupHomomorphism = isGroupHomomorphism ≈₃-trans F.+-isGroupHomomorphism G.+-isGroupHomomorphism
    ; *-homo                 = λ x y → ≈₃-trans (G.⟦⟧-cong (F.*-homo x y)) (G.*-homo (f x) (f y))
    } where module F = IsRingWithoutOneHomomorphism f-homo; module G = IsRingWithoutOneHomomorphism g-homo

  isRingWithoutOneMonomorphism
    : IsRingWithoutOneMonomorphism R₁ R₂ f
    → IsRingWithoutOneMonomorphism R₂ R₃ g
    → IsRingWithoutOneMonomorphism R₁ R₃ (g ∘ f)
  isRingWithoutOneMonomorphism f-mono g-mono = record
    { isRingWithoutOneHomomorphism = isRingWithoutOneHomomorphism F.isRingWithoutOneHomomorphism G.isRingWithoutOneHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsRingWithoutOneMonomorphism f-mono;  module G = IsRingWithoutOneMonomorphism g-mono

  isRingWithoutOneIsoMorphism
    : IsRingWithoutOneIsoMorphism R₁ R₂ f
    → IsRingWithoutOneIsoMorphism R₂ R₃ g
    → IsRingWithoutOneIsoMorphism R₁ R₃ (g ∘ f)
  isRingWithoutOneIsoMorphism f-iso g-iso = record
    { isRingWithoutOneMonomorphism = isRingWithoutOneMonomorphism F.isRingWithoutOneMonomorphism G.isRingWithoutOneMonomorphism
    ; surjective         = Func.surjective _ _ (_≈_ R₃) F.surjective G.surjective
    } where module F = IsRingWithoutOneIsoMorphism f-iso; module G = IsRingWithoutOneIsoMorphism g-iso

------------------------------------------------------------------------
-- Rings

module _ {R₁ : RawRing a ℓ₁}
         {R₂ : RawRing b ℓ₂}
         {R₃ : RawRing c ℓ₃}
         (open RawRing)
         (≈₃-trans : Transitive (_≈_ R₃))
         {f : Carrier R₁ → Carrier R₂}
         {g : Carrier R₂ → Carrier R₃}
         where


  isRingHomomorphism
    : IsRingHomomorphism R₁ R₂ f
    → IsRingHomomorphism R₂ R₃ g
    → IsRingHomomorphism R₁ R₃ (g ∘ f)
  isRingHomomorphism f-homo g-homo = record
    { isSemiringHomomorphism = isSemiringHomomorphism ≈₃-trans F.isSemiringHomomorphism G.isSemiringHomomorphism
    ; -‿homo                 = λ x → ≈₃-trans (G.⟦⟧-cong (F.-‿homo x)) (G.-‿homo (f x))
    } where module F = IsRingHomomorphism f-homo; module G = IsRingHomomorphism g-homo

  isRingMonomorphism
    : IsRingMonomorphism R₁ R₂ f
    → IsRingMonomorphism R₂ R₃ g
    → IsRingMonomorphism R₁ R₃ (g ∘ f)
  isRingMonomorphism f-mono g-mono = record
    { isRingHomomorphism = isRingHomomorphism F.isRingHomomorphism G.isRingHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsRingMonomorphism f-mono;  module G = IsRingMonomorphism g-mono

  isRingIsomorphism
    : IsRingIsomorphism R₁ R₂ f
    → IsRingIsomorphism R₂ R₃ g
    → IsRingIsomorphism R₁ R₃ (g ∘ f)
  isRingIsomorphism f-iso g-iso = record
    { isRingMonomorphism = isRingMonomorphism F.isRingMonomorphism G.isRingMonomorphism
    ; surjective         = Func.surjective _ _ (_≈_ R₃) F.surjective G.surjective
    } where module F = IsRingIsomorphism f-iso; module G = IsRingIsomorphism g-iso

------------------------------------------------------------------------
-- Quasigroup

module _ {Q₁ : RawQuasigroup a ℓ₁}
         {Q₂ : RawQuasigroup b ℓ₂}
         {Q₃ : RawQuasigroup c ℓ₃}
         (open RawQuasigroup)
         (≈₃-trans : Transitive (_≈_ Q₃))
         {f : Carrier Q₁ → Carrier Q₂}
         {g : Carrier Q₂ → Carrier Q₃}
         where


  isQuasigroupHomomorphism
    : IsQuasigroupHomomorphism Q₁ Q₂ f
    → IsQuasigroupHomomorphism Q₂ Q₃ g
    → IsQuasigroupHomomorphism Q₁ Q₃ (g ∘ f)
  isQuasigroupHomomorphism f-homo g-homo = record
    { isRelHomomorphism = isRelHomomorphism F.isRelHomomorphism G.isRelHomomorphism
    ; ∙-homo              = λ x y → ≈₃-trans (G.⟦⟧-cong ( F.∙-homo x y )) ( G.∙-homo (f x) (f y) )
    ; \\-homo              = λ x y → ≈₃-trans (G.⟦⟧-cong ( F.\\-homo x y )) ( G.\\-homo (f x) (f y) )
    ; //-homo              = λ x y → ≈₃-trans (G.⟦⟧-cong ( F.//-homo x y )) ( G.//-homo (f x) (f y) )
    } where module F = IsQuasigroupHomomorphism f-homo; module G = IsQuasigroupHomomorphism g-homo

  isQuasigroupMonomorphism
    : IsQuasigroupMonomorphism Q₁ Q₂ f
    → IsQuasigroupMonomorphism Q₂ Q₃ g
    → IsQuasigroupMonomorphism Q₁ Q₃ (g ∘ f)
  isQuasigroupMonomorphism f-mono g-mono = record
    { isQuasigroupHomomorphism = isQuasigroupHomomorphism F.isQuasigroupHomomorphism G.isQuasigroupHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsQuasigroupMonomorphism f-mono;  module G = IsQuasigroupMonomorphism g-mono

  isQuasigroupIsomorphism
    : IsQuasigroupIsomorphism Q₁ Q₂ f
    → IsQuasigroupIsomorphism Q₂ Q₃ g
    → IsQuasigroupIsomorphism Q₁ Q₃ (g ∘ f)
  isQuasigroupIsomorphism f-iso g-iso = record
    { isQuasigroupMonomorphism = isQuasigroupMonomorphism F.isQuasigroupMonomorphism G.isQuasigroupMonomorphism
    ; surjective               = Func.surjective _ _ (_≈_ Q₃) F.surjective G.surjective
    } where module F = IsQuasigroupIsomorphism f-iso; module G = IsQuasigroupIsomorphism g-iso

------------------------------------------------------------------------
-- Loop

module _ {L₁ : RawLoop a ℓ₁}
         {L₂ : RawLoop b ℓ₂}
         {L₃ : RawLoop c ℓ₃}
         (open RawLoop)
         (≈₃-trans : Transitive (_≈_ L₃))
         {f : Carrier L₁ → Carrier L₂}
         {g : Carrier L₂ → Carrier L₃}
         where


  isLoopHomomorphism
    : IsLoopHomomorphism L₁ L₂ f
    → IsLoopHomomorphism L₂ L₃ g
    → IsLoopHomomorphism L₁ L₃ (g ∘ f)
  isLoopHomomorphism f-homo g-homo = record
    { isQuasigroupHomomorphism = isQuasigroupHomomorphism ≈₃-trans F.isQuasigroupHomomorphism G.isQuasigroupHomomorphism
    ; ε-homo              = ≈₃-trans (G.⟦⟧-cong F.ε-homo) G.ε-homo
    } where module F = IsLoopHomomorphism f-homo; module G = IsLoopHomomorphism g-homo

  isLoopMonomorphism
    : IsLoopMonomorphism L₁ L₂ f
    → IsLoopMonomorphism L₂ L₃ g
    → IsLoopMonomorphism L₁ L₃ (g ∘ f)
  isLoopMonomorphism f-mono g-mono = record
    { isLoopHomomorphism = isLoopHomomorphism F.isLoopHomomorphism G.isLoopHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsLoopMonomorphism f-mono;  module G = IsLoopMonomorphism g-mono

  isLoopIsomorphism
    : IsLoopIsomorphism L₁ L₂ f
    → IsLoopIsomorphism L₂ L₃ g
    → IsLoopIsomorphism L₁ L₃ (g ∘ f)
  isLoopIsomorphism f-iso g-iso = record
    { isLoopMonomorphism = isLoopMonomorphism F.isLoopMonomorphism G.isLoopMonomorphism
    ; surjective         = Func.surjective _ _ (_≈_ L₃) F.surjective G.surjective
    } where module F = IsLoopIsomorphism f-iso; module G = IsLoopIsomorphism g-iso

------------------------------------------------------------------------
-- KleeneAlgebra

module _ {K₁ : RawKleeneAlgebra a ℓ₁}
         {K₂ : RawKleeneAlgebra b ℓ₂}
         {K₃ : RawKleeneAlgebra c ℓ₃}
         (open RawKleeneAlgebra)
         (≈₃-trans : Transitive (_≈_ K₃))
         {f : Carrier K₁ → Carrier K₂}
         {g : Carrier K₂ → Carrier K₃}
         where

  isKleeneAlgebraHomomorphism
    : IsKleeneAlgebraHomomorphism K₁ K₂ f
    → IsKleeneAlgebraHomomorphism K₂ K₃ g
    → IsKleeneAlgebraHomomorphism K₁ K₃ (g ∘ f)
  isKleeneAlgebraHomomorphism f-homo g-homo = record
    { isSemiringHomomorphism = isSemiringHomomorphism ≈₃-trans F.isSemiringHomomorphism G.isSemiringHomomorphism
    ; ⋆-homo              = λ x → ≈₃-trans (G.⟦⟧-cong (F.⋆-homo x)) (G.⋆-homo (f x))
    } where module F = IsKleeneAlgebraHomomorphism f-homo; module G = IsKleeneAlgebraHomomorphism g-homo

  isKleeneAlgebraMonomorphism
    : IsKleeneAlgebraMonomorphism K₁ K₂ f
    → IsKleeneAlgebraMonomorphism K₂ K₃ g
    → IsKleeneAlgebraMonomorphism K₁ K₃ (g ∘ f)
  isKleeneAlgebraMonomorphism f-mono g-mono = record
    { isKleeneAlgebraHomomorphism = isKleeneAlgebraHomomorphism F.isKleeneAlgebraHomomorphism G.isKleeneAlgebraHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsKleeneAlgebraMonomorphism f-mono;  module G = IsKleeneAlgebraMonomorphism g-mono

  isKleeneAlgebraIsomorphism
    : IsKleeneAlgebraIsomorphism K₁ K₂ f
    → IsKleeneAlgebraIsomorphism K₂ K₃ g
    → IsKleeneAlgebraIsomorphism K₁ K₃ (g ∘ f)
  isKleeneAlgebraIsomorphism f-iso g-iso = record
    { isKleeneAlgebraMonomorphism = isKleeneAlgebraMonomorphism F.isKleeneAlgebraMonomorphism G.isKleeneAlgebraMonomorphism
    ; surjective                  = Func.surjective (_≈_ K₁) (_≈_ K₂) (_≈_ K₃) F.surjective G.surjective
    } where module F = IsKleeneAlgebraIsomorphism f-iso; module G = IsKleeneAlgebraIsomorphism g-iso

-----------------------------------------------------------------------
-- Bundled morphisms between algebras
------------------------------------------------------------------------

-- Magma

module _ {M₁ : Magma a ℓ₁} {M₂ : Magma b ℓ₂} {M₃ : Magma c ℓ₃} where

  private
    module M₁ = Magma M₁
    module M₂ = Magma M₂
    module M₃ = Magma M₃

  magmaHomomorphism : (h : MagmaHomomorphism M₁.rawMagma M₂.rawMagma) →
                      (k : MagmaHomomorphism M₂.rawMagma M₃.rawMagma) →
                      MagmaHomomorphism M₁.rawMagma M₃.rawMagma
  magmaHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isMagmaHomomorphism = isMagmaHomomorphism M₃.trans H.isMagmaHomomorphism K.isMagmaHomomorphism
    }
    where
    module H = MagmaHomomorphism h
    module K = MagmaHomomorphism k

-- Monoid

module _ {M₁ : Monoid a ℓ₁} {M₂ : Monoid b ℓ₂} {M₃ : Monoid c ℓ₃} where

  private
    module M₁ = Monoid M₁
    module M₂ = Monoid M₂
    module M₃ = Monoid M₃

  monoidHomomorphism : (h : MonoidHomomorphism M₁.rawMonoid M₂.rawMonoid) →
                       (k : MonoidHomomorphism M₂.rawMonoid M₃.rawMonoid) →
                       MonoidHomomorphism M₁.rawMonoid M₃.rawMonoid
  monoidHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isMonoidHomomorphism = isMonoidHomomorphism M₃.trans H.isMonoidHomomorphism K.isMonoidHomomorphism
    }
    where
    module H = MonoidHomomorphism h
    module K = MonoidHomomorphism k

-- Group

module _ {M₁ : Group a ℓ₁} {M₂ : Group b ℓ₂} {M₃ : Group c ℓ₃} where

  private
    module M₁ = Group M₁
    module M₂ = Group M₂
    module M₃ = Group M₃

  groupHomomorphism : (h : GroupHomomorphism M₁.rawGroup M₂.rawGroup) →
                      (k : GroupHomomorphism M₂.rawGroup M₃.rawGroup) →
                      GroupHomomorphism M₁.rawGroup M₃.rawGroup
  groupHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isGroupHomomorphism = isGroupHomomorphism M₃.trans H.isGroupHomomorphism K.isGroupHomomorphism
    }
    where
    module H = GroupHomomorphism h
    module K = GroupHomomorphism k

-- NearSemiring

module _ {M₁ : NearSemiring a ℓ₁} {M₂ : NearSemiring b ℓ₂} {M₃ : NearSemiring c ℓ₃} where

  private
    module M₁ = NearSemiring M₁
    module M₂ = NearSemiring M₂
    module M₃ = NearSemiring M₃

  nearSemiringHomomorphism : (h : NearSemiringHomomorphism M₁.rawNearSemiring M₂.rawNearSemiring) →
                             (k : NearSemiringHomomorphism M₂.rawNearSemiring M₃.rawNearSemiring) →
                             NearSemiringHomomorphism M₁.rawNearSemiring M₃.rawNearSemiring
  nearSemiringHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isNearSemiringHomomorphism = isNearSemiringHomomorphism M₃.trans H.isNearSemiringHomomorphism K.isNearSemiringHomomorphism
    }
    where
    module H = NearSemiringHomomorphism h
    module K = NearSemiringHomomorphism k

-- Semiring

module _ {M₁ : Semiring a ℓ₁} {M₂ : Semiring b ℓ₂} {M₃ : Semiring c ℓ₃} where

  private
    module M₁ = Semiring M₁
    module M₂ = Semiring M₂
    module M₃ = Semiring M₃

  semiringHomomorphism : (h : SemiringHomomorphism M₁.rawSemiring M₂.rawSemiring) →
                         (k : SemiringHomomorphism M₂.rawSemiring M₃.rawSemiring) →
                         SemiringHomomorphism M₁.rawSemiring M₃.rawSemiring
  semiringHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isSemiringHomomorphism = isSemiringHomomorphism M₃.trans H.isSemiringHomomorphism K.isSemiringHomomorphism
    }
    where
    module H = SemiringHomomorphism h
    module K = SemiringHomomorphism k

-- RingWithoutOne

module _ {M₁ : RingWithoutOne a ℓ₁} {M₂ : RingWithoutOne b ℓ₂} {M₃ : RingWithoutOne c ℓ₃} where

  private
    module M₁ = RingWithoutOne M₁
    module M₂ = RingWithoutOne M₂
    module M₃ = RingWithoutOne M₃

  ringWithoutOneHomomorphism : (h : RingWithoutOneHomomorphism M₁.rawRingWithoutOne M₂.rawRingWithoutOne) →
                               (k : RingWithoutOneHomomorphism M₂.rawRingWithoutOne M₃.rawRingWithoutOne) →
                               RingWithoutOneHomomorphism M₁.rawRingWithoutOne M₃.rawRingWithoutOne
  ringWithoutOneHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isRingWithoutOneHomomorphism = isRingWithoutOneHomomorphism M₃.trans H.isRingWithoutOneHomomorphism K.isRingWithoutOneHomomorphism
    }
    where
    module H = RingWithoutOneHomomorphism h
    module K = RingWithoutOneHomomorphism k

-- Ring

module _ {M₁ : Ring a ℓ₁} {M₂ : Ring b ℓ₂} {M₃ : Ring c ℓ₃} where

  private
    module M₁ = Ring M₁
    module M₂ = Ring M₂
    module M₃ = Ring M₃

  ringHomomorphism : (h : RingHomomorphism M₁.rawRing M₂.rawRing) →
                     (k : RingHomomorphism M₂.rawRing M₃.rawRing) →
                     RingHomomorphism M₁.rawRing M₃.rawRing
  ringHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isRingHomomorphism = isRingHomomorphism M₃.trans H.isRingHomomorphism K.isRingHomomorphism
    }
    where
    module H = RingHomomorphism h
    module K = RingHomomorphism k

-- Quasigroup

module _ {M₁ : Quasigroup a ℓ₁} {M₂ : Quasigroup b ℓ₂} {M₃ : Quasigroup c ℓ₃} where

  private
    module M₁ = Quasigroup M₁
    module M₂ = Quasigroup M₂
    module M₃ = Quasigroup M₃

  quasigroupHomomorphism : (h : QuasigroupHomomorphism M₁.rawQuasigroup M₂.rawQuasigroup) →
                           (k : QuasigroupHomomorphism M₂.rawQuasigroup M₃.rawQuasigroup) →
                           QuasigroupHomomorphism M₁.rawQuasigroup M₃.rawQuasigroup
  quasigroupHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isQuasigroupHomomorphism = isQuasigroupHomomorphism M₃.trans H.isQuasigroupHomomorphism K.isQuasigroupHomomorphism
    }
    where
    module H = QuasigroupHomomorphism h
    module K = QuasigroupHomomorphism k

-- Loop

module _ {M₁ : Loop a ℓ₁} {M₂ : Loop b ℓ₂} {M₃ : Loop c ℓ₃} where

  private
    module M₁ = Loop M₁
    module M₂ = Loop M₂
    module M₃ = Loop M₃

  loopHomomorphism : (h : LoopHomomorphism M₁.rawLoop M₂.rawLoop) →
                     (k : LoopHomomorphism M₂.rawLoop M₃.rawLoop) →
                     LoopHomomorphism M₁.rawLoop M₃.rawLoop
  loopHomomorphism h k = record
    { ⟦_⟧ = K.⟦_⟧ ∘ H.⟦_⟧
    ; isLoopHomomorphism = isLoopHomomorphism M₃.trans H.isLoopHomomorphism K.isLoopHomomorphism
    }
    where
    module H = LoopHomomorphism h
    module K = LoopHomomorphism k


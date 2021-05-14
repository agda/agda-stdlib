------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Algebra.Morphism.Construct.Composition where

open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Data.Product
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Composition

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  {M₁ : Magma a ℓ₁} {M₂ : Magma b ℓ₂} {M₃ : Magma c ℓ₃}
  {f : Magma.Carrier M₁ → Magma.Carrier M₂}
  {g : Magma.Carrier M₂ → Magma.Carrier M₃}
  where

  open Magma
  private
    module M₁ = Magma M₁
    module M₂ = Magma M₂
    module M₃ = Magma M₃

  isMagmaHomomorphism
    : IsMagmaHomomorphism M₁.rawMagma M₂.rawMagma f
    → IsMagmaHomomorphism M₂.rawMagma M₃.rawMagma g
    → IsMagmaHomomorphism M₁.rawMagma M₃.rawMagma (g ∘ f)
  isMagmaHomomorphism f-homo g-homo = record
    { isRelHomomorphism = isRelHomomorphism f-homo.isRelHomomorphism g-homo.isRelHomomorphism
    ; homo = λ x y → M₃.trans (g-homo.⟦⟧-cong (f-homo.homo x y)) (g-homo.homo (f x) (f y))
    }
    where
      module f-homo = IsMagmaHomomorphism f-homo
      module g-homo = IsMagmaHomomorphism g-homo

  isMagmaMonomorphism
    : IsMagmaMonomorphism M₁.rawMagma M₂.rawMagma f
    → IsMagmaMonomorphism M₂.rawMagma M₃.rawMagma g
    → IsMagmaMonomorphism M₁.rawMagma M₃.rawMagma (g ∘ f)
  isMagmaMonomorphism f-mono g-mono = record
    { isMagmaHomomorphism = isMagmaHomomorphism f-mono.isMagmaHomomorphism g-mono.isMagmaHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsMagmaMonomorphism f-mono
      module g-mono = IsMagmaMonomorphism g-mono

  isMagmaIsomorphism
    : IsMagmaIsomorphism M₁.rawMagma M₂.rawMagma f
    → IsMagmaIsomorphism M₂.rawMagma M₃.rawMagma g
    → IsMagmaIsomorphism M₁.rawMagma M₃.rawMagma (g ∘ f)
  isMagmaIsomorphism f-iso g-iso = record
    { isMagmaMonomorphism = isMagmaMonomorphism f-iso.isMagmaMonomorphism g-iso.isMagmaMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , M₃.trans (g-iso.⟦⟧-cong q) p
    }
    where
      module f-iso = IsMagmaIsomorphism f-iso
      module g-iso = IsMagmaIsomorphism g-iso

module _
  {M₁ : Monoid a ℓ₁} {M₂ : Monoid b ℓ₂} {M₃ : Monoid c ℓ₃}
  {f : Monoid.Carrier M₁ → Monoid.Carrier M₂}
  {g : Monoid.Carrier M₂ → Monoid.Carrier M₃}
  where

  open Monoid
  private
    module M₁ = Monoid M₁
    module M₂ = Monoid M₂
    module M₃ = Monoid M₃

  isMonoidHomomorphism
    : IsMonoidHomomorphism M₁.rawMonoid M₂.rawMonoid f
    → IsMonoidHomomorphism M₂.rawMonoid M₃.rawMonoid g
    → IsMonoidHomomorphism M₁.rawMonoid M₃.rawMonoid (g ∘ f)
  isMonoidHomomorphism f-homo g-homo = record
    { isMagmaHomomorphism = isMagmaHomomorphism
      {M₁ = M₁.magma} {M₂ = M₂.magma} {M₃ = M₃.magma}
      f-homo.isMagmaHomomorphism g-homo.isMagmaHomomorphism
    ; ε-homo = M₃.trans (g-homo.⟦⟧-cong (f-homo.ε-homo)) g-homo.ε-homo
    }
    where
      module f-homo = IsMonoidHomomorphism f-homo
      module g-homo = IsMonoidHomomorphism g-homo

  isMonoidMonomorphism
    : IsMonoidMonomorphism M₁.rawMonoid M₂.rawMonoid f
    → IsMonoidMonomorphism M₂.rawMonoid M₃.rawMonoid g
    → IsMonoidMonomorphism M₁.rawMonoid M₃.rawMonoid (g ∘ f)
  isMonoidMonomorphism f-mono g-mono = record
    { isMonoidHomomorphism = isMonoidHomomorphism f-mono.isMonoidHomomorphism g-mono.isMonoidHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsMonoidMonomorphism f-mono
      module g-mono = IsMonoidMonomorphism g-mono

  isMonoidIsomorphism
    : IsMonoidIsomorphism M₁.rawMonoid M₂.rawMonoid f
    → IsMonoidIsomorphism M₂.rawMonoid M₃.rawMonoid g
    → IsMonoidIsomorphism M₁.rawMonoid M₃.rawMonoid (g ∘ f)
  isMonoidIsomorphism f-iso g-iso = record
    { isMonoidMonomorphism = isMonoidMonomorphism f-iso.isMonoidMonomorphism g-iso.isMonoidMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , M₃.trans (g-iso.⟦⟧-cong q) p
    }
    where
      module f-iso = IsMonoidIsomorphism f-iso
      module g-iso = IsMonoidIsomorphism g-iso

module _
  {G₁ : Group a ℓ₁} {G₂ : Group b ℓ₂} {G₃ : Group c ℓ₃}
  {f : Group.Carrier G₁ → Group.Carrier G₂}
  {g : Group.Carrier G₂ → Group.Carrier G₃}
  where

  open Group
  private
    module G₁ = Group G₁
    module G₂ = Group G₂
    module G₃ = Group G₃

  isGroupHomomorphism
    : IsGroupHomomorphism G₁.rawGroup G₂.rawGroup f
    → IsGroupHomomorphism G₂.rawGroup G₃.rawGroup g
    → IsGroupHomomorphism G₁.rawGroup G₃.rawGroup (g ∘ f)
  isGroupHomomorphism f-homo g-homo = record
    { isMonoidHomomorphism = isMonoidHomomorphism
      {M₁ = G₁.monoid} {M₂ = G₂.monoid} {M₃ = G₃.monoid}
      f-homo.isMonoidHomomorphism g-homo.isMonoidHomomorphism
    ; ⁻¹-homo = λ x → G₃.trans (g-homo.⟦⟧-cong (f-homo.⁻¹-homo x)) (g-homo.⁻¹-homo (f x))
    }
    where
      module f-homo = IsGroupHomomorphism f-homo
      module g-homo = IsGroupHomomorphism g-homo

  isGroupMonomorphism
    : IsGroupMonomorphism G₁.rawGroup G₂.rawGroup f
    → IsGroupMonomorphism G₂.rawGroup G₃.rawGroup g
    → IsGroupMonomorphism G₁.rawGroup G₃.rawGroup (g ∘ f)
  isGroupMonomorphism f-mono g-mono = record
    { isGroupHomomorphism = isGroupHomomorphism f-mono.isGroupHomomorphism g-mono.isGroupHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsGroupMonomorphism f-mono
      module g-mono = IsGroupMonomorphism g-mono

  isGroupIsomorphism
    : IsGroupIsomorphism G₁.rawGroup G₂.rawGroup f
    → IsGroupIsomorphism G₂.rawGroup G₃.rawGroup g
    → IsGroupIsomorphism G₁.rawGroup G₃.rawGroup (g ∘ f)
  isGroupIsomorphism f-iso g-iso = record
    { isGroupMonomorphism = isGroupMonomorphism f-iso.isGroupMonomorphism g-iso.isGroupMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , G₃.trans (g-iso.⟦⟧-cong q) p
    }
    where
      module f-iso = IsGroupIsomorphism f-iso
      module g-iso = IsGroupIsomorphism g-iso

module _
  {R₁ : NearSemiring a ℓ₁} {R₂ : NearSemiring b ℓ₂} {R₃ : NearSemiring c ℓ₃}
  {f : NearSemiring.Carrier R₁ → NearSemiring.Carrier R₂}
  {g : NearSemiring.Carrier R₂ → NearSemiring.Carrier R₃}
  where

  open NearSemiring
  private
    module R₁ = NearSemiring R₁
    module R₂ = NearSemiring R₂
    module R₃ = NearSemiring R₃

  isNearSemiringHomomorphism
    : IsNearSemiringHomomorphism R₁.rawNearSemiring R₂.rawNearSemiring f
    → IsNearSemiringHomomorphism R₂.rawNearSemiring R₃.rawNearSemiring g
    → IsNearSemiringHomomorphism R₁.rawNearSemiring R₃.rawNearSemiring (g ∘ f)
  isNearSemiringHomomorphism f-homo g-homo = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism
      {M₁ = R₁.+-monoid} {M₂ = R₂.+-monoid} {M₃ = R₃.+-monoid}
      f-homo.+-isMonoidHomomorphism g-homo.+-isMonoidHomomorphism
    ; *-isMagmaHomomorphism = isMagmaHomomorphism
      {M₁ = R₁.*-magma} {M₂ = R₂.*-magma} {M₃ = R₃.*-magma}
      f-homo.*-isMagmaHomomorphism g-homo.*-isMagmaHomomorphism
    }
    where
      module f-homo = IsNearSemiringHomomorphism f-homo
      module g-homo = IsNearSemiringHomomorphism g-homo

  isNearSemiringMonomorphism
    : IsNearSemiringMonomorphism R₁.rawNearSemiring R₂.rawNearSemiring f
    → IsNearSemiringMonomorphism R₂.rawNearSemiring R₃.rawNearSemiring g
    → IsNearSemiringMonomorphism R₁.rawNearSemiring R₃.rawNearSemiring (g ∘ f)
  isNearSemiringMonomorphism f-mono g-mono = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism f-mono.isNearSemiringHomomorphism g-mono.isNearSemiringHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsNearSemiringMonomorphism f-mono
      module g-mono = IsNearSemiringMonomorphism g-mono

  isNearSemiringIsomorphism
    : IsNearSemiringIsomorphism R₁.rawNearSemiring R₂.rawNearSemiring f
    → IsNearSemiringIsomorphism R₂.rawNearSemiring R₃.rawNearSemiring g
    → IsNearSemiringIsomorphism R₁.rawNearSemiring R₃.rawNearSemiring (g ∘ f)
  isNearSemiringIsomorphism f-iso g-iso = record
    { isNearSemiringMonomorphism = isNearSemiringMonomorphism f-iso.isNearSemiringMonomorphism g-iso.isNearSemiringMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , R₃.trans (IsMonoidHomomorphism.⟦⟧-cong (g-iso.+-isMonoidHomomorphism) q) p
    }
    where
      module f-iso = IsNearSemiringIsomorphism f-iso
      module g-iso = IsNearSemiringIsomorphism g-iso

module _
  {R₁ : Semiring a ℓ₁} {R₂ : Semiring b ℓ₂} {R₃ : Semiring c ℓ₃}
  {f : Semiring.Carrier R₁ → Semiring.Carrier R₂}
  {g : Semiring.Carrier R₂ → Semiring.Carrier R₃}
  where

  open Semiring
  private
    module R₁ = Semiring R₁
    module R₂ = Semiring R₂
    module R₃ = Semiring R₃

  isSemiringHomomorphism
    : IsSemiringHomomorphism R₁.rawSemiring R₂.rawSemiring f
    → IsSemiringHomomorphism R₂.rawSemiring R₃.rawSemiring g
    → IsSemiringHomomorphism R₁.rawSemiring R₃.rawSemiring (g ∘ f)
  isSemiringHomomorphism f-homo g-homo = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism
      {M₁ = R₁.+-monoid} {M₂ = R₂.+-monoid} {M₃ = R₃.+-monoid}
      f-homo.+-isMonoidHomomorphism g-homo.+-isMonoidHomomorphism
    ; *-isMonoidHomomorphism = isMonoidHomomorphism
      {M₁ = R₁.*-monoid} {M₂ = R₂.*-monoid} {M₃ = R₃.*-monoid}
      f-homo.*-isMonoidHomomorphism g-homo.*-isMonoidHomomorphism
    }
    where
      module f-homo = IsSemiringHomomorphism f-homo
      module g-homo = IsSemiringHomomorphism g-homo

  isSemiringMonomorphism
    : IsSemiringMonomorphism R₁.rawSemiring R₂.rawSemiring f
    → IsSemiringMonomorphism R₂.rawSemiring R₃.rawSemiring g
    → IsSemiringMonomorphism R₁.rawSemiring R₃.rawSemiring (g ∘ f)
  isSemiringMonomorphism f-mono g-mono = record
    { isSemiringHomomorphism = isSemiringHomomorphism f-mono.isSemiringHomomorphism g-mono.isSemiringHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsSemiringMonomorphism f-mono
      module g-mono = IsSemiringMonomorphism g-mono

  isSemiringIsomorphism
    : IsSemiringIsomorphism R₁.rawSemiring R₂.rawSemiring f
    → IsSemiringIsomorphism R₂.rawSemiring R₃.rawSemiring g
    → IsSemiringIsomorphism R₁.rawSemiring R₃.rawSemiring (g ∘ f)
  isSemiringIsomorphism f-iso g-iso = record
    { isSemiringMonomorphism = isSemiringMonomorphism f-iso.isSemiringMonomorphism g-iso.isSemiringMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , R₃.trans (IsMonoidHomomorphism.⟦⟧-cong (g-iso.+-isMonoidHomomorphism) q) p
    }
    where
      module f-iso = IsSemiringIsomorphism f-iso
      module g-iso = IsSemiringIsomorphism g-iso

module _
  {R₁ : Ring a ℓ₁} {R₂ : Ring b ℓ₂} {R₃ : Ring c ℓ₃}
  {f : Ring.Carrier R₁ → Ring.Carrier R₂}
  {g : Ring.Carrier R₂ → Ring.Carrier R₃}
  where

  open Ring
  private
    module R₁ = Ring R₁
    module R₂ = Ring R₂
    module R₃ = Ring R₃

  isRingHomomorphism
    : IsRingHomomorphism R₁.rawRing R₂.rawRing f
    → IsRingHomomorphism R₂.rawRing R₃.rawRing g
    → IsRingHomomorphism R₁.rawRing R₃.rawRing (g ∘ f)
  isRingHomomorphism f-homo g-homo = record
    { +-isGroupHomomorphism = isGroupHomomorphism
      {G₁ = R₁.+-group} {G₂ = R₂.+-group} {G₃ = R₃.+-group}
      f-homo.+-isGroupHomomorphism g-homo.+-isGroupHomomorphism
    ; *-isMonoidHomomorphism = isMonoidHomomorphism
      {M₁ = R₁.*-monoid} {M₂ = R₂.*-monoid} {M₃ = R₃.*-monoid}
      f-homo.*-isMonoidHomomorphism g-homo.*-isMonoidHomomorphism
    }
    where
      module f-homo = IsRingHomomorphism f-homo
      module g-homo = IsRingHomomorphism g-homo

  isRingMonomorphism
    : IsRingMonomorphism R₁.rawRing R₂.rawRing f
    → IsRingMonomorphism R₂.rawRing R₃.rawRing g
    → IsRingMonomorphism R₁.rawRing R₃.rawRing (g ∘ f)
  isRingMonomorphism f-mono g-mono = record
    { isRingHomomorphism = isRingHomomorphism f-mono.isRingHomomorphism g-mono.isRingHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsRingMonomorphism f-mono
      module g-mono = IsRingMonomorphism g-mono

  isRingIsomorphism
    : IsRingIsomorphism R₁.rawRing R₂.rawRing f
    → IsRingIsomorphism R₂.rawRing R₃.rawRing g
    → IsRingIsomorphism R₁.rawRing R₃.rawRing (g ∘ f)
  isRingIsomorphism f-iso g-iso = record
    { isRingMonomorphism = isRingMonomorphism f-iso.isRingMonomorphism g-iso.isRingMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , R₃.trans (IsGroupHomomorphism.⟦⟧-cong (g-iso.+-isGroupHomomorphism) q) p
    }
    where
      module f-iso = IsRingIsomorphism f-iso
      module g-iso = IsRingIsomorphism g-iso

module _
  {L₁ : Lattice a ℓ₁} {L₂ : Lattice b ℓ₂} {L₃ : Lattice c ℓ₃}
  {f : Lattice.Carrier L₁ → Lattice.Carrier L₂}
  {g : Lattice.Carrier L₂ → Lattice.Carrier L₃}
  where

  open Lattice
  private
    module L₁ = Lattice L₁
    module L₂ = Lattice L₂
    module L₃ = Lattice L₃

  isLatticeHomomorphism
    : IsLatticeHomomorphism L₁.rawLattice L₂.rawLattice f
    → IsLatticeHomomorphism L₂.rawLattice L₃.rawLattice g
    → IsLatticeHomomorphism L₁.rawLattice L₃.rawLattice (g ∘ f)
  isLatticeHomomorphism f-homo g-homo = record
    { ∧-isMagmaHomomorphism = isMagmaHomomorphism
      {M₁ = L₁.∧-magma} {M₂ = L₂.∧-magma} {M₃ = L₃.∧-magma}
      f-homo.∧-isMagmaHomomorphism g-homo.∧-isMagmaHomomorphism
    ; ∨-isMagmaHomomorphism = isMagmaHomomorphism
      {M₁ = L₁.∨-magma} {M₂ = L₂.∨-magma} {M₃ = L₃.∨-magma}
      f-homo.∨-isMagmaHomomorphism g-homo.∨-isMagmaHomomorphism
    }
    where
      module f-homo = IsLatticeHomomorphism f-homo
      module g-homo = IsLatticeHomomorphism g-homo

  isLatticeMonomorphism
    : IsLatticeMonomorphism L₁.rawLattice L₂.rawLattice f
    → IsLatticeMonomorphism L₂.rawLattice L₃.rawLattice g
    → IsLatticeMonomorphism L₁.rawLattice L₃.rawLattice (g ∘ f)
  isLatticeMonomorphism f-mono g-mono = record
    { isLatticeHomomorphism = isLatticeHomomorphism f-mono.isLatticeHomomorphism g-mono.isLatticeHomomorphism
    ; injective = f-mono.injective ∘ g-mono.injective
    }
    where
      module f-mono = IsLatticeMonomorphism f-mono
      module g-mono = IsLatticeMonomorphism g-mono

  isLatticeIsomorphism
    : IsLatticeIsomorphism L₁.rawLattice L₂.rawLattice f
    → IsLatticeIsomorphism L₂.rawLattice L₃.rawLattice g
    → IsLatticeIsomorphism L₁.rawLattice L₃.rawLattice (g ∘ f)
  isLatticeIsomorphism f-iso g-iso = record
    { isLatticeMonomorphism = isLatticeMonomorphism f-iso.isLatticeMonomorphism g-iso.isLatticeMonomorphism
    ; surjective = λ x →
      let
        x′ , p = g-iso.surjective x
        x″ , q = f-iso.surjective x′
      in x″ , L₃.trans (IsMagmaHomomorphism.⟦⟧-cong (g-iso.∧-isMagmaHomomorphism) q) p
    }
    where
      module f-iso = IsLatticeIsomorphism f-iso
      module g-iso = IsLatticeIsomorphism g-iso

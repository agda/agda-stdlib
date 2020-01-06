------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism where

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Relation.Binary
open import Algebra
import Algebra.Properties.Group as GroupP
open import Function
open import Level
import Relation.Binary.Reasoning.Setoid as EqR

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
--

module Definitions {a b ℓ₁} (A : Set a) (B : Set b) (_≈_ : Rel B ℓ₁) where
  open MorphismDefinitions A B _≈_ public

open import Algebra.Morphism.Structures public

------------------------------------------------------------------------
-- Bundle homomorphisms

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Semigroup c₁ ℓ₁)
         (To   : Semigroup c₂ ℓ₂) where

  private
    module F = Semigroup From
    module T = Semigroup To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsSemigroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
      ∙-homo  : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_

  IsSemigroupMorphism-syntax = IsSemigroupMorphism
  syntax IsSemigroupMorphism-syntax From To F = F Is From -Semigroup⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Monoid c₁ ℓ₁)
         (To   : Monoid c₂ ℓ₂) where

  private
    module F = Monoid From
    module T = Monoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      sm-homo : IsSemigroupMorphism F.semigroup T.semigroup ⟦_⟧
      ε-homo  : Homomorphic₀ ⟦_⟧ F.ε T.ε

    open IsSemigroupMorphism sm-homo public

  IsMonoidMorphism-syntax = IsMonoidMorphism
  syntax IsMonoidMorphism-syntax From To F = F Is From -Monoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : CommutativeMonoid c₁ ℓ₁)
         (To   : CommutativeMonoid c₂ ℓ₂) where

  private
    module F = CommutativeMonoid From
    module T = CommutativeMonoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsCommutativeMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

  IsCommutativeMonoidMorphism-syntax = IsCommutativeMonoidMorphism
  syntax IsCommutativeMonoidMorphism-syntax From To F = F Is From -CommutativeMonoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : IdempotentCommutativeMonoid c₁ ℓ₁)
         (To   : IdempotentCommutativeMonoid c₂ ℓ₂) where

  private
    module F = IdempotentCommutativeMonoid From
    module T = IdempotentCommutativeMonoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsIdempotentCommutativeMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

    isCommutativeMonoidMorphism :
      IsCommutativeMonoidMorphism F.commutativeMonoid T.commutativeMonoid ⟦_⟧
    isCommutativeMonoidMorphism = record { mn-homo = mn-homo }

  IsIdempotentCommutativeMonoidMorphism-syntax = IsIdempotentCommutativeMonoidMorphism
  syntax IsIdempotentCommutativeMonoidMorphism-syntax From To F = F Is From -IdempotentCommutativeMonoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Group c₁ ℓ₁)
         (To   : Group c₂ ℓ₂) where

  private
    module F = Group From
    module T = Group To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsGroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

    ⁻¹-homo : Homomorphic₁ ⟦_⟧ F._⁻¹ T._⁻¹
    ⁻¹-homo x = let open EqR T.setoid in T.uniqueˡ-⁻¹ ⟦ x F.⁻¹ ⟧ ⟦ x ⟧ $ begin
      ⟦ x F.⁻¹ ⟧ T.∙ ⟦ x ⟧ ≈⟨ T.sym (∙-homo (x F.⁻¹) x) ⟩
      ⟦ x F.⁻¹ F.∙ x ⟧     ≈⟨ ⟦⟧-cong (F.inverseˡ x) ⟩
      ⟦ F.ε ⟧              ≈⟨ ε-homo ⟩
      T.ε ∎

  IsGroupMorphism-syntax = IsGroupMorphism
  syntax IsGroupMorphism-syntax From To F = F Is From -Group⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : AbelianGroup c₁ ℓ₁)
         (To   : AbelianGroup c₂ ℓ₂) where

  private
    module F = AbelianGroup From
    module T = AbelianGroup To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsAbelianGroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      gp-homo : IsGroupMorphism F.group T.group ⟦_⟧

    open IsGroupMorphism gp-homo public

  IsAbelianGroupMorphism-syntax = IsAbelianGroupMorphism
  syntax IsAbelianGroupMorphism-syntax From To F = F Is From -AbelianGroup⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Ring c₁ ℓ₁)
         (To   : Ring c₂ ℓ₂) where

  private
    module F = Ring From
    module T = Ring To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsRingMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      +-abgp-homo : ⟦_⟧ Is F.+-abelianGroup -AbelianGroup⟶ T.+-abelianGroup
      *-mn-homo   : ⟦_⟧ Is F.*-monoid -Monoid⟶ T.*-monoid

  IsRingMorphism-syntax = IsRingMorphism
  syntax IsRingMorphism-syntax From To F = F Is From -Ring⟶ To

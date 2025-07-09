------------------------------------------------------------------------
-- The Agda standard library
--
-- The structure of a group
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Structures.IsGroup
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
open import Algebra.Structures.IsMagma _≈_
open import Algebra.Structures.IsMonoid _≈_
open import Algebra.Structures.IsQuasigroup _≈_
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definition

record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMonoid isMonoid public

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse

  isInvertibleMagma : IsInvertibleMagma _∙_ ε _⁻¹
  isInvertibleMagma = record
    { isMagma = isMagma
    ; inverse = inverse
    ; ⁻¹-cong = ⁻¹-cong
    }

  isInvertibleUnitalMagma : IsInvertibleUnitalMagma _∙_ ε _⁻¹
  isInvertibleUnitalMagma = record
    { isInvertibleMagma = isInvertibleMagma
    ; identity = identity
    }

  infixr 6 _\\_
  _\\_ : Op₂ A
  x \\ y = (x ⁻¹) ∙ y

  infixl 6 _//_
  _//_ : Op₂ A
  x // y = x ∙ (y ⁻¹)

  \\-cong₂ : Congruent₂ _\\_
  \\-cong₂ x≈y u≈v = ∙-cong (⁻¹-cong x≈y) u≈v

  //-cong₂ : Congruent₂ _//_
  //-cong₂ x≈y u≈v = ∙-cong x≈y (⁻¹-cong u≈v)

  open import Relation.Binary.Reasoning.Setoid setoid

  \\-leftDividesˡ : LeftDividesˡ _∙_ _\\_
  \\-leftDividesˡ x y = begin
    x ∙ (x \\ y)  ≈⟨ assoc x (x ⁻¹) y ⟨
    (x ∙ (x ⁻¹)) ∙ y   ≈⟨ ∙-congʳ (inverseʳ x) ⟩
    ε ∙ y          ≈⟨ identityˡ y ⟩
    y              ∎

  \\-leftDividesʳ : LeftDividesʳ _∙_ _\\_
  \\-leftDividesʳ x y = begin
    x \\ (x ∙ y)     ≈⟨ assoc (x ⁻¹) x y ⟨
    ((x ⁻¹) ∙ x) ∙ y   ≈⟨ ∙-congʳ (inverseˡ x) ⟩
    ε ∙ y          ≈⟨ identityˡ y ⟩
    y              ∎

  \\-leftDivides : LeftDivides _∙_ _\\_
  \\-leftDivides = \\-leftDividesˡ , \\-leftDividesʳ

  //-rightDividesˡ : RightDividesˡ _∙_ _//_
  //-rightDividesˡ x y = begin
    (y // x) ∙ x    ≈⟨ assoc y (x ⁻¹) x ⟩
    y ∙ ((x ⁻¹) ∙ x)  ≈⟨ ∙-congˡ (inverseˡ x) ⟩
    y ∙ ε           ≈⟨ identityʳ y ⟩
    y               ∎

  //-rightDividesʳ : RightDividesʳ _∙_ _//_
  //-rightDividesʳ x y = begin
    y ∙ x // x    ≈⟨ assoc y x (x ⁻¹) ⟩
    y ∙ (x // x)  ≈⟨ ∙-congˡ (inverseʳ x) ⟩
    y ∙ ε         ≈⟨ identityʳ y ⟩
    y             ∎

  //-rightDivides : RightDivides _∙_ _//_
  //-rightDivides = //-rightDividesˡ , //-rightDividesʳ

  isQuasigroup : IsQuasigroup _∙_ _\\_ _//_
  isQuasigroup = record
    { isMagma = isMagma
    ; \\-cong = \\-cong₂
    ; //-cong = //-cong₂
    ; leftDivides = \\-leftDivides
    ; rightDivides = //-rightDivides
    }

  isLoop : IsLoop _∙_ _\\_ _//_ ε
  isLoop = record { isQuasigroup = isQuasigroup ; identity = identity }


record IsAbelianGroup (∙ : Op₂ A)
                      (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public renaming (_//_ to _-_) hiding (_\\_)

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeMagma; isCommutativeSemigroup)

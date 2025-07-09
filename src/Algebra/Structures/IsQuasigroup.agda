------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Structures.IsQuasigroup
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
open import Algebra.Structures.IsMagma _≈_
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Quasigroups
------------------------------------------------------------------------

record IsQuasigroup (∙ \\ // : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma       : IsMagma ∙
    \\-cong       : Congruent₂ \\
    //-cong       : Congruent₂ //
    leftDivides   : LeftDivides ∙ \\
    rightDivides  : RightDivides ∙ //

  open IsMagma isMagma public

  \\-congˡ : LeftCongruent \\
  \\-congˡ y≈z = \\-cong refl y≈z

  \\-congʳ : RightCongruent \\
  \\-congʳ y≈z = \\-cong y≈z refl

  //-congˡ : LeftCongruent //
  //-congˡ y≈z = //-cong refl y≈z

  //-congʳ : RightCongruent //
  //-congʳ y≈z = //-cong y≈z refl

  leftDividesˡ : LeftDividesˡ ∙ \\
  leftDividesˡ = proj₁ leftDivides

  leftDividesʳ : LeftDividesʳ ∙ \\
  leftDividesʳ = proj₂ leftDivides

  rightDividesˡ : RightDividesˡ ∙ //
  rightDividesˡ = proj₁ rightDivides

  rightDividesʳ : RightDividesʳ ∙ //
  rightDividesʳ = proj₂ rightDivides


record IsLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isQuasigroup : IsQuasigroup ∙ \\ //
    identity     : Identity ε ∙

  open IsQuasigroup isQuasigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

record IsLeftBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop  : IsLoop ∙ \\ //  ε
    leftBol : LeftBol ∙

  open IsLoop isLoop public

record IsRightBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop   : IsLoop ∙ \\ //  ε
    rightBol : RightBol ∙

  open IsLoop isLoop public

record IsMoufangLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLeftBolLoop  : IsLeftBolLoop ∙ \\ //  ε
    rightBol       : RightBol ∙
    identical      : Identical ∙

  open IsLeftBolLoop isLeftBolLoop public

record IsMiddleBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop    : IsLoop ∙ \\ //  ε
    middleBol : MiddleBol ∙ \\ //

  open IsLoop isLoop public

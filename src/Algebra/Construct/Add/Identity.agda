------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of algebraic structures we get from freely adding an
-- identity element
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.Add.Identity where

open import Algebra.Bundles
open import Algebra.Core using (Op₂)
open import Algebra.Definitions
open import Algebra.Structures
open import Relation.Binary.Construct.Add.Point.Equality renaming (_≈∙_ to lift≈)
open import Data.Product.Base using (_,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Nullary.Construct.Add.Point

private
  variable
    a ℓ : Level
    A : Set a

liftOp : Op₂ A → Op₂ (Pointed A)
liftOp op [ p ] [ q ] = [ op p q ]
liftOp _  [ p ] ∙     = [ p ]
liftOp _  ∙     [ q ] = [ q ]
liftOp _  ∙     ∙     = ∙

module _ {_≈_ : Rel A ℓ} {op : Op₂ A} (refl-≈ : Reflexive _≈_) where
  private
    _≈∙_ = lift≈ _≈_
    op∙ = liftOp op

    lift-≈ : ∀ {x y : A} → x ≈ y → [ x ] ≈∙ [ y ]
    lift-≈ = [_]

  cong₂ : Congruent₂ _≈_ op → Congruent₂ _≈∙_ (op∙)
  cong₂ R-cong [ eq-l ] [ eq-r ] = lift-≈ (R-cong eq-l eq-r)
  cong₂ R-cong [ eq   ] ∙≈∙      = lift-≈ eq
  cong₂ R-cong ∙≈∙      [ eq   ] = lift-≈ eq
  cong₂ R-cong ∙≈∙      ∙≈∙      = ≈∙-refl _≈_ refl-≈

  assoc : Associative _≈_ op → Associative _≈∙_ (op∙)
  assoc assoc [ p ] [ q ] [ r ] = lift-≈ (assoc p q r)
  assoc _     [ p ] [ q ] ∙     = ≈∙-refl _≈_ refl-≈
  assoc _     [ p ] ∙     [ r ] = ≈∙-refl _≈_ refl-≈
  assoc _     [ p ] ∙     ∙     = ≈∙-refl _≈_ refl-≈
  assoc _     ∙     [ r ] [ q ] = ≈∙-refl _≈_ refl-≈
  assoc _     ∙     [ q ] ∙     = ≈∙-refl _≈_ refl-≈
  assoc _     ∙     ∙     [ r ] = ≈∙-refl _≈_ refl-≈
  assoc _     ∙     ∙     ∙     = ≈∙-refl _≈_ refl-≈

  identityˡ : LeftIdentity _≈∙_ ∙ (op∙)
  identityˡ [ p ] = ≈∙-refl _≈_ refl-≈
  identityˡ ∙     = ≈∙-refl _≈_ refl-≈

  identityʳ : RightIdentity _≈∙_ ∙ (op∙)
  identityʳ [ p ] = ≈∙-refl _≈_ refl-≈
  identityʳ ∙     = ≈∙-refl _≈_ refl-≈

  identity : Identity _≈∙_ ∙ (op∙)
  identity = identityˡ , identityʳ

module _ {_≈_ : Rel A ℓ} {op : Op₂ A} where
  private
    _≈∙_ = lift≈ _≈_
    op∙ = liftOp op

  isMagma : IsMagma _≈_ op → IsMagma _≈∙_ op∙
  isMagma M =
    record
    { isEquivalence = ≈∙-isEquivalence _≈_ M.isEquivalence
    ; ∙-cong        = cong₂ M.refl M.∙-cong
    } where module M = IsMagma M

  isSemigroup : IsSemigroup _≈_ op → IsSemigroup _≈∙_ op∙
  isSemigroup S = record
    { isMagma = isMagma S.isMagma
    ; assoc   = assoc S.refl S.assoc
    } where module S = IsSemigroup S

  isMonoid : IsSemigroup _≈_ op → IsMonoid _≈∙_ op∙ ∙
  isMonoid S = record
    { isSemigroup = isSemigroup S
    ; identity    = identity S.refl
    } where module S = IsSemigroup S

semigroup : Semigroup a (a ⊔ ℓ) → Semigroup a (a ⊔ ℓ)
semigroup S = record
  { Carrier = Pointed S.Carrier
  ; isSemigroup = isSemigroup S.isSemigroup
  } where module S = Semigroup S

monoid : Semigroup a (a ⊔ ℓ) → Monoid a (a ⊔ ℓ)
monoid S = record
  { isMonoid = isMonoid S.isSemigroup
  } where module S = Semigroup S

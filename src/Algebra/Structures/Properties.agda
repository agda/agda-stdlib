------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Algebra.Structures.Properties where

open import Algebra.FunctionProperties
open import Algebra.Structures
open import Relation.Binary
open import Data.Product
open import Function.Core

module _ {a ℓ₁ ℓ₂} {A : Set a} {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel A ℓ₂}
         (equiv@(to , from) : _≈₁_ ⇔ _≈₂_)
         where

  isEquivalence : IsEquivalence _≈₁_ → IsEquivalence _≈₂_
  isEquivalence E = record
    { refl  = to E.refl
    ; sym   = to ∘′ E.sym ∘′ from
    ; trans = λ p q → to (E.trans (from p) (from q))
    } where module E = IsEquivalence E

  congruent : ∀ {∙} → Congruent₂ _≈₁_ ∙ → Congruent₂ _≈₂_ ∙
  congruent C u≈v x≈y = to (C (from u≈v) (from x≈y))

  isMagma : ∀ {∙} → IsMagma _≈₁_ ∙ → IsMagma _≈₂_ ∙
  isMagma M = record
    { isEquivalence = isEquivalence M.isEquivalence
    ; ∙-cong        = congruent M.∙-cong
    } where module M = IsMagma M

  isSemigroup : ∀ {∙} → IsSemigroup _≈₁_ ∙ → IsSemigroup _≈₂_ ∙
  isSemigroup S = record
    { isMagma = isMagma S.isMagma
    ; assoc   = λ x y z → to (S.assoc x y z)
    } where module S = IsSemigroup S

  isBand : ∀ {∙} → IsBand _≈₁_ ∙ → IsBand _≈₂_ ∙
  isBand B = record
    { isSemigroup = isSemigroup B.isSemigroup
    ; idem        = to ∘ B.idem
    } where module B = IsBand B

  isSemilattice : ∀ {∧} → IsSemilattice _≈₁_ ∧ → IsSemilattice _≈₂_ ∧
  isSemilattice S = record
    { isBand = isBand S.isBand
    ; comm   = λ x y → to (S.comm x y)
    } where module S = IsSemilattice S


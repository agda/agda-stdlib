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
open import Data.Product as Prod
import Data.Sum as Sum
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

  isSelectiveMagma : ∀ {∙} → IsSelectiveMagma _≈₁_ ∙ → IsSelectiveMagma _≈₂_ ∙
  isSelectiveMagma SM = record
    { isMagma = isMagma SM.isMagma
    ; sel     = λ x y → Sum.map to to (SM.sel x y)
    } where module SM = IsSelectiveMagma SM

  isMonoid : ∀ {∙ ε} → IsMonoid _≈₁_ ∙ ε → IsMonoid _≈₂_ ∙ ε
  isMonoid M = record
    { isSemigroup = isSemigroup M.isSemigroup
    ; identity    = Prod.map (to ∘_) (to ∘_) (M.identity)
    } where module M = IsMonoid M

  isCommutativeMonoid : ∀ {∙ ε} →
    IsCommutativeMonoid _≈₁_ ∙ ε → IsCommutativeMonoid _≈₂_ ∙ ε
  isCommutativeMonoid CM = record
    { isSemigroup = isSemigroup CM.isSemigroup
    ; identityˡ   = to ∘ CM.identityˡ
    ; comm        = λ x y → to (CM.comm x y)
    } where module CM = IsCommutativeMonoid CM

  isIdempotentCommutativeMonoid : ∀ {∙ ε} →
    IsIdempotentCommutativeMonoid _≈₁_ ∙ ε →
    IsIdempotentCommutativeMonoid _≈₂_ ∙ ε
  isIdempotentCommutativeMonoid ICM = record
    { isCommutativeMonoid = isCommutativeMonoid ICM.isCommutativeMonoid
    ; idem                = to ∘ ICM.idem
    } where module ICM = IsIdempotentCommutativeMonoid ICM

  isGroup : ∀ {op ε inv} → IsGroup _≈₁_ op ε inv → IsGroup _≈₂_ op ε inv
  isGroup G = record
    { isMonoid = isMonoid G.isMonoid
    ; inverse  = Prod.map (to ∘_) (to ∘_) G.inverse
    ; ⁻¹-cong  = to ∘′ G.⁻¹-cong ∘′ from
    } where module G = IsGroup G


  isAbelianGroup : ∀ {op ε inv} →
    IsAbelianGroup _≈₁_ op ε inv → IsAbelianGroup _≈₂_ op ε inv
  isAbelianGroup AG = record
    { isGroup = isGroup AG.isGroup
    ; comm    = λ x y → to (AG.comm x y)
    } where module AG = IsAbelianGroup AG

  isLattice : ∀ {∨ ∧} → IsLattice _≈₁_ ∨ ∧ → IsLattice _≈₂_ ∨ ∧
  isLattice L = record
    { isEquivalence = isEquivalence L.isEquivalence
    ; ∨-comm        = λ x y → to (L.∨-comm x y)
    ; ∨-assoc       = λ x y z → to (L.∨-assoc x y z)
    ; ∨-cong        = congruent L.∨-cong
    ; ∧-comm        = λ x y → to (L.∧-comm x y)
    ; ∧-assoc       = λ x y z → to (L.∧-assoc x y z)
    ; ∧-cong        = congruent L.∧-cong
    ; absorptive    = Prod.map (λ f x y → to (f x y)) (λ f x y → to (f x y))
                      L.absorptive
    } where module L = IsLattice L

  isDistributiveLattice : ∀ {∨ ∧} →
    IsDistributiveLattice _≈₁_ ∨ ∧ → IsDistributiveLattice _≈₂_ ∨ ∧
  isDistributiveLattice DL = record
    { isLattice    = isLattice DL.isLattice
    ; ∨-distribʳ-∧ = λ x y z → to (DL.∨-distribʳ-∧ x y z)
    } where module DL = IsDistributiveLattice DL

  isNearSemiring : ∀ {+ * 0#} →
    IsNearSemiring _≈₁_ + * 0# → IsNearSemiring _≈₂_ + * 0#
  isNearSemiring NS = record
    { +-isMonoid    = isMonoid NS.+-isMonoid
    ; *-isSemigroup = isSemigroup NS.*-isSemigroup
    ; distribʳ      = λ x y z → to (NS.distribʳ x y z)
    ; zeroˡ         = to ∘ NS.zeroˡ
    } where module NS = IsNearSemiring NS

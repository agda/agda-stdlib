------------------------------------------------------------------------
-- The Agda standard library
--
-- Substituting equalities for binary relations
------------------------------------------------------------------------

-- For more general transformations between algebraic structures see
-- `Algebra.Morphisms`.

{-# OPTIONS --without-K --safe #-}

open import Data.Product.Base as Product
open import Relation.Binary.Core using (Rel; _⇔_)

module Algebra.Construct.Subst.Equality
  {a ℓ₁ ℓ₂} {A : Set a} {≈₁ : Rel A ℓ₁} {≈₂ : Rel A ℓ₂}
  (equiv@(to , from) : ≈₁ ⇔ ≈₂)
  where

open import Algebra.Definitions
open import Algebra.Structures
import Data.Sum.Base as Sum
open import Function.Base using (id; _∘_)
open import Relation.Binary.Construct.Subst.Equality equiv

------------------------------------------------------------------------
-- Definitions

cong₁ : ∀ {⁻¹} → Congruent₁ ≈₁ ⁻¹ → Congruent₁ ≈₂ ⁻¹
cong₁ cong x≈y = to (cong (from x≈y))

cong₂ : ∀ {∙} → Congruent₂ ≈₁ ∙ → Congruent₂ ≈₂ ∙
cong₂ cong u≈v x≈y = to (cong (from u≈v) (from x≈y))

assoc : ∀ {∙} → Associative ≈₁ ∙ → Associative ≈₂ ∙
assoc assoc x y z = to (assoc x y z)

comm : ∀ {∙} → Commutative ≈₁ ∙ → Commutative ≈₂ ∙
comm comm x y = to (comm x y)

idem : ∀ {∙} → Idempotent ≈₁ ∙ → Idempotent ≈₂ ∙
idem idem x = to (idem x)

sel : ∀ {∙} → Selective ≈₁ ∙ → Selective ≈₂ ∙
sel sel x y = Sum.map to to (sel x y)

identity : ∀ {∙ e} → Identity ≈₁ e ∙ → Identity ≈₂ e ∙
identity = Product.map (to ∘_) (to ∘_)

inverse : ∀ {∙ e ⁻¹} → Inverse ≈₁ ⁻¹ ∙ e → Inverse ≈₂ ⁻¹ ∙ e
inverse = Product.map (to ∘_) (to ∘_)

absorptive : ∀ {∙ ◦} → Absorptive ≈₁ ∙ ◦ → Absorptive ≈₂ ∙ ◦
absorptive = Product.map (λ f x y → to (f x y)) (λ f x y → to (f x y))

distribˡ : ∀ {∙ ◦} → _DistributesOverˡ_ ≈₁ ∙ ◦ → _DistributesOverˡ_ ≈₂ ∙ ◦
distribˡ distribˡ x y z = to (distribˡ x y z)

distribʳ : ∀ {∙ ◦} → _DistributesOverʳ_ ≈₁ ∙ ◦ → _DistributesOverʳ_ ≈₂ ∙ ◦
distribʳ distribʳ x y z = to (distribʳ x y z)

distrib : ∀ {∙ ◦} → _DistributesOver_ ≈₁ ∙ ◦ → _DistributesOver_ ≈₂ ∙ ◦
distrib {∙} {◦} = Product.map (distribˡ {∙} {◦}) (distribʳ {∙} {◦})

------------------------------------------------------------------------
-- Structures

isMagma : ∀ {∙} → IsMagma ≈₁ ∙ → IsMagma ≈₂ ∙
isMagma S = record
  { isEquivalence = isEquivalence S.isEquivalence
  ; ∙-cong        = cong₂ S.∙-cong
  } where module S = IsMagma S

isSemigroup : ∀ {∙} → IsSemigroup ≈₁ ∙ → IsSemigroup ≈₂ ∙
isSemigroup {∙} S = record
  { isMagma = isMagma S.isMagma
  ; assoc   = assoc {∙} S.assoc
  } where module S = IsSemigroup S

isBand : ∀ {∙} → IsBand ≈₁ ∙ → IsBand ≈₂ ∙
isBand {∙} S = record
  { isSemigroup = isSemigroup S.isSemigroup
  ; idem        = idem {∙} S.idem
  } where module S = IsBand S

isSelectiveMagma : ∀ {∙} → IsSelectiveMagma ≈₁ ∙ → IsSelectiveMagma ≈₂ ∙
isSelectiveMagma S = record
  { isMagma = isMagma S.isMagma
  ; sel     = sel S.sel
  } where module S = IsSelectiveMagma S

isMonoid : ∀ {∙ ε} → IsMonoid ≈₁ ∙ ε → IsMonoid ≈₂ ∙ ε
isMonoid S = record
  { isSemigroup = isSemigroup S.isSemigroup
  ; identity    = Product.map (to ∘_) (to ∘_) S.identity
  } where module S = IsMonoid S

isCommutativeMonoid : ∀ {∙ ε} →
  IsCommutativeMonoid ≈₁ ∙ ε → IsCommutativeMonoid ≈₂ ∙ ε
isCommutativeMonoid S = record
  { isMonoid = isMonoid S.isMonoid
  ; comm     = comm S.comm
  } where module S = IsCommutativeMonoid S

isIdempotentCommutativeMonoid : ∀ {∙ ε} →
  IsIdempotentCommutativeMonoid ≈₁ ∙ ε →
  IsIdempotentCommutativeMonoid ≈₂ ∙ ε
isIdempotentCommutativeMonoid {∙} S = record
  { isCommutativeMonoid = isCommutativeMonoid S.isCommutativeMonoid
  ; idem                = to ∘ S.idem
  } where module S = IsIdempotentCommutativeMonoid S

isGroup : ∀ {∙ ε ⁻¹} → IsGroup ≈₁ ∙ ε ⁻¹ → IsGroup ≈₂ ∙ ε ⁻¹
isGroup S = record
  { isMonoid = isMonoid S.isMonoid
  ; inverse  = Product.map (to ∘_) (to ∘_) S.inverse
  ; ⁻¹-cong  = cong₁ S.⁻¹-cong
  } where module S = IsGroup S

isAbelianGroup : ∀ {∙ ε ⁻¹} →
  IsAbelianGroup ≈₁ ∙ ε ⁻¹ → IsAbelianGroup ≈₂ ∙ ε ⁻¹
isAbelianGroup S = record
  { isGroup = isGroup S.isGroup
  ; comm    = comm S.comm
  } where module S = IsAbelianGroup S

isNearSemiring : ∀ {+ * 0#} →
  IsNearSemiring ≈₁ + * 0# → IsNearSemiring ≈₂ + * 0#
isNearSemiring {* = *} S = record
  { +-isMonoid    = isMonoid S.+-isMonoid
  ; *-cong        = cong₂ S.*-cong
  ; *-assoc       = assoc {*} S.*-assoc
  ; distribʳ      = λ x y z → to (S.distribʳ x y z)
  ; zeroˡ         = to ∘ S.zeroˡ
  } where module S = IsNearSemiring S

isSemiringWithoutOne : ∀ {+ * 0#} →
  IsSemiringWithoutOne ≈₁ + * 0# → IsSemiringWithoutOne ≈₂ + * 0#
isSemiringWithoutOne {+} {*} S = record
  { +-isCommutativeMonoid = isCommutativeMonoid S.+-isCommutativeMonoid
  ; *-cong                = cong₂ S.*-cong
  ; *-assoc               = assoc {*} S.*-assoc
  ; distrib               = distrib {*} {+} S.distrib
  ; zero                  = Product.map (to ∘_) (to ∘_) S.zero
  } where module S = IsSemiringWithoutOne S

isCommutativeSemiringWithoutOne : ∀ {+ * 0#} →
  IsCommutativeSemiringWithoutOne ≈₁ + * 0# →
  IsCommutativeSemiringWithoutOne ≈₂ + * 0#
isCommutativeSemiringWithoutOne S = record
  { isSemiringWithoutOne = isSemiringWithoutOne S.isSemiringWithoutOne
  ; *-comm               = comm S.*-comm
  } where module S = IsCommutativeSemiringWithoutOne S

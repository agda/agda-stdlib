------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
  using (BooleanSemiring; BooleanRing
        ; CommutativeMonoid; IdempotentCommutativeMonoid
        ; Ring; CommutativeRing)

module Algebra.Properties.BooleanSemiring
  {c ℓ} (booleanSemiring : BooleanSemiring c ℓ) where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Lattice.Bundles
  using (DistributiveLattice; BooleanAlgebra)
import Algebra.Properties.CommutativeMonoid as CommutativeMonoidProperties
import Algebra.Properties.IdempotentCommutativeMonoid as IdempotentCommutativeMonoidProperties
import Algebra.Lattice.Properties.DistributiveLattice as DistributiveLatticeProperties
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_)

open BooleanSemiring booleanSemiring
import Algebra.Consequences.Setoid setoid as Consequences
open import Algebra.Definitions _≈_
open import Algebra.Lattice.Structures.Biased _≈_
  using (IsLattice₂; isLattice₂
        ; IsDistributiveLatticeʳʲᵐ; isDistributiveLatticeʳʲᵐ
        ; IsBooleanAlgebraʳ; isBooleanAlgebraʳ
        )
open import Algebra.Lattice.Structures _≈_
  using (IsLattice; IsDistributiveLattice; IsBooleanAlgebra)
open import Algebra.Structures _≈_
  using (IsMagma; IsSemigroup; IsBand
        ; IsCommutativeMonoid; IsIdempotentCommutativeMonoid
        ; IsGroup; IsAbelianGroup
        ; IsRing; IsCommutativeRing; IsBooleanRing
        )
open import Relation.Binary.Reasoning.Setoid setoid


------------------------------------------------------------------------
-- Re-export Semiring properties

open import Algebra.Properties.Semiring semiring public

------------------------------------------------------------------------
-- Extra properties of Boolean semirings

xy+yx≈0 : ∀ x y → x * y + y * x ≈ 0#
xy+yx≈0 x y = +-cancelˡ (x * x) _ _ $ +-cancelʳ (y * y) _ _ $ begin
  x * x + ((x * y) + (y * x)) + y * y ≈⟨ +-congʳ (+-assoc _ _ _) ⟨
  x * x + x * y + y * x + y * y       ≈⟨ binomial-expansion x y x y ⟨
  (x + y) * (x + y)                   ≈⟨ *-idem (x + y) ⟩
  x + y                               ≈⟨ +-congˡ (*-idem y) ⟨
  x + y * y                           ≈⟨ +-congʳ (*-idem x) ⟨
  x * x + y * y                       ≈⟨ +-congʳ (+-identityʳ (x * x)) ⟨
  x * x + 0# + y * y                  ∎

y≈x⇒x+y≈0 : ∀ {x y} → y ≈ x → x + y ≈ 0#
y≈x⇒x+y≈0 {x = x} {y = y} y≈x = begin
  x + y         ≈⟨ +-cong (*-idem x) (*-idem y) ⟨
  x * x + y * y ≈⟨ +-cong (*-congˡ (sym y≈x)) (*-congˡ y≈x) ⟩
  x * y + y * x ≈⟨ xy+yx≈0 x y ⟩
  0#            ∎

x+x≈0 : ∀ x → x + x ≈ 0#
x+x≈0 x = y≈x⇒x+y≈0 refl

x+y≈0⇒y≈x : ∀ {x y} → x + y ≈ 0# → y ≈ x
x+y≈0⇒y≈x {x = x} {y = y} x+y≈0 = +-cancelˡ x _ _ $ begin
  x + y  ≈⟨ x+y≈0 ⟩
  0#     ≈⟨ x+x≈0 x ⟨
  x + x  ∎

*-comm : Commutative _*_
*-comm x y = +-cancelʳ (y * x) _ _ $ begin
  x * y + y * x ≈⟨ xy+yx≈0 x y ⟩
  0#            ≈⟨ x+x≈0 (y * x) ⟨
  y * x + y * x ∎

------------------------------------------------------------------------
-- Additional structures

+-isGroup : IsGroup _+_ 0# id
+-isGroup = record { isMonoid = +-isMonoid ; inverse = x+x≈0 , x+x≈0 ; ⁻¹-cong = id }

+-isAbelianGroup : IsAbelianGroup _+_ 0# id
+-isAbelianGroup = record { isGroup = +-isGroup ; comm = +-comm }

*-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
*-isCommutativeMonoid = record { isMonoid = *-isMonoid ; comm = *-comm }

*-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _*_ 1#
*-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  ; idem = *-idem
  }

open IsIdempotentCommutativeMonoid *-isIdempotentCommutativeMonoid public
  using () renaming (isCommutativeBand to *-isCommutativeBand)

isRing : IsRing _+_ _*_ id 0# 1#
isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-cong = *-cong
  ; *-assoc = *-assoc
  ; *-identity = *-identity
  ; distrib = distrib
  }

isCommutativeRing : IsCommutativeRing _+_ _*_ id 0# 1#
isCommutativeRing = record { isRing = isRing ; *-comm = *-comm }

isBooleanRing : IsBooleanRing _+_ _*_ id 0# 1#
isBooleanRing = record { isCommutativeRing = isCommutativeRing ; *-idem = *-idem }

------------------------------------------------------------------------
-- Additional bundles

*-commutativeMonoid : CommutativeMonoid _ _
*-commutativeMonoid = record { isCommutativeMonoid = *-isCommutativeMonoid }

*-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
*-idempotentCommutativeMonoid = record
  { isIdempotentCommutativeMonoid = *-isIdempotentCommutativeMonoid }

open IdempotentCommutativeMonoid *-idempotentCommutativeMonoid public
  using () renaming (commutativeBand to *-commutativeBand)

commutativeRing : CommutativeRing _ _
commutativeRing = record { isCommutativeRing = isCommutativeRing }

open CommutativeRing commutativeRing public
  using (ring)

booleanRing : BooleanRing _ _
booleanRing = record { isBooleanRing = isBooleanRing }

------------------------------------------------------------------------
-- Boolean Semirings yield Boolean Algebras

-- Definitions

infix  8 ¬_
¬_ : Op₁ Carrier
¬ x = 1# + x

¬-cong : Congruent₁ ¬_
¬-cong = +-congˡ

¬-involutive : Involutive ¬_
¬-involutive x = begin
  ¬ ¬ x         ≡⟨⟩
  1# + (1# + x) ≈⟨ +-assoc 1# 1# x ⟨
  1# + 1# + x   ≈⟨ +-congʳ (x+x≈0 1#) ⟩
  0# + x        ≈⟨ +-identityˡ x ⟩
  x             ∎

∧-complementʳ : RightInverse 0# ¬_ _*_
∧-complementʳ x = begin
  x * (¬ x)      ≈⟨ distribˡ x 1# x ⟩
  x * 1# + x * x ≈⟨ +-cong (*-identityʳ x) (*-idem x) ⟩
  x + x          ≈⟨ x+x≈0 x ⟩
  0#             ∎

private
  *-lemma : ∀ x y → x + (x * ¬ x) * y ≈ x
  *-lemma x y = begin
    x + (x * ¬ x) * y     ≈⟨ +-congˡ (*-congʳ (∧-complementʳ x)) ⟩
    x + 0# * y            ≈⟨ +-congˡ (zeroˡ y) ⟩
    x + 0#                ≈⟨ +-identityʳ _ ⟩
    x                     ∎

infixr 6 _∨_
_∨_ : Op₂ Carrier
x ∨ y = x + y * ¬ x

-- Basic properties

∨-complementʳ : RightInverse 1# ¬_ _∨_
∨-complementʳ x = begin
  x ∨ ¬ x      ≈⟨ +-congˡ (*-idem (¬ x)) ⟩
  x + ¬ x      ≈⟨ x∙yz≈y∙xz x 1# x ⟩
  1# + (x + x) ≈⟨ +-congˡ (x+x≈0 x) ⟩
  1# + 0#      ≈⟨ +-identityʳ _ ⟩
  1#           ∎
  where open CommutativeMonoidProperties +-commutativeMonoid

∨-def : ∀ x y → x ∨ y ≈ x + y + x * y
∨-def x y = begin
  x ∨ y                ≈⟨ +-congˡ (distribˡ y 1# x) ⟩
  x + (y * 1# + y * x) ≈⟨ +-assoc x (y * 1#) (y * x) ⟨
  x + y * 1# + y * x   ≈⟨ +-cong (+-congˡ (*-identityʳ y)) (*-comm y x) ⟩
  x + y + x * y        ∎

∨-cong : Congruent₂ _∨_
∨-cong x≈x′ y≈y′ = +-cong x≈x′ (*-cong y≈y′ (¬-cong x≈x′))

∨-comm : Commutative _∨_
∨-comm x y = begin
  x ∨ y         ≈⟨ ∨-def x y ⟩
  x + y + x * y ≈⟨ +-cong (+-comm x y) (*-comm x y) ⟩
  y + x + y * x ≈⟨ ∨-def y x ⟨
  y ∨ x         ∎

∨-idem : Idempotent _∨_
∨-idem x = begin
  x ∨ x   ≈⟨ +-congˡ (∧-complementʳ x) ⟩
  x + 0#  ≈⟨ +-identityʳ x ⟩
  x       ∎

deMorgan₁ : ∀ x y → ¬ (x * y) ≈ ¬ x ∨ ¬ y
deMorgan₁ x y = begin
  ¬ (x * y)                 ≡⟨⟩
  1# + x * y                ≈⟨ +-cong (+-identityʳ 1#) (*-comm y x) ⟨
  1# + 0# + y * x           ≈⟨ +-congʳ (+-congˡ (x+x≈0 x)) ⟨
  1# + (x + x) + y * x      ≈⟨ +-congʳ (+-assoc 1# x x) ⟨
  1# + x + x + y * x        ≈⟨ +-congʳ (+-congˡ (*-identityˡ x)) ⟨
  1# + x + 1# * x + y * x   ≈⟨ +-assoc (1# + x) (1# * x) (y * x) ⟩
  1# + x + (1# * x + y * x) ≈⟨ +-congˡ (distribʳ x 1# y) ⟨
  1# + x + ¬ y * x          ≈⟨ +-congˡ (*-congˡ (¬-involutive x)) ⟨
  ¬ x + ¬ y * ¬ ¬ x         ≡⟨⟩
  ¬ x ∨ ¬ y                 ∎

deMorgan₂ : ∀ x y → ¬ (x ∨ y) ≈ ¬ x * ¬ y
deMorgan₂ x y = begin
  ¬ (x ∨ y)                         ≈⟨ +-congˡ (∨-def x y) ⟩
  1# + (x + y + x * y)              ≈⟨ +-assoc _ _ _ ⟨
  1# + (x + y) + x * y              ≈⟨ +-congʳ (x∙yz≈xz∙y 1# x y) ⟩
  1# + y + x + x * y                ≈⟨ +-congʳ (+-cong (+-cong (*-idem _) (*-identityˡ y)) (*-identityʳ x)) ⟨
  1# * 1# + 1# * y + x * 1# + x * y ≈⟨ binomial-expansion 1# x 1# y ⟨
  (1# + x) * (1# + y)               ≡⟨⟩
  ¬ x * ¬ y ∎
  where open CommutativeMonoidProperties +-commutativeMonoid

∨-assoc : Associative _∨_
∨-assoc x y z = begin
  (x ∨ y) ∨ z           ≈⟨ ¬-involutive ((x ∨ y) ∨ z) ⟨
  ¬ ¬ ((x ∨ y) ∨ z)     ≈⟨ ¬-cong (deMorgan₂ (x ∨ y) z) ⟩
  ¬ (¬ (x ∨ y) * ¬ z)   ≈⟨ ¬-cong (*-congʳ (deMorgan₂ x y)) ⟩
  ¬ ((¬ x * ¬ y) * ¬ z) ≈⟨ ¬-cong (*-assoc (¬ x) (¬ y) (¬ z)) ⟩
  ¬ (¬ x * (¬ y * ¬ z)) ≈⟨ ¬-cong (*-congˡ (deMorgan₂ y z)) ⟨
  ¬ (¬ x * ¬ (y ∨ z))   ≈⟨ ¬-cong (deMorgan₂ x (y ∨ z)) ⟨
  ¬ ¬ (x ∨ y ∨ z)       ≈⟨ ¬-involutive (x ∨ y ∨ z) ⟩
  x ∨ y ∨ z ∎

-- Lattice properties

∨-absorbs-* : _∨_ Absorbs _*_
∨-absorbs-* x y = begin
  x ∨ x * y         ≈⟨ +-congˡ (xy∙z≈xz∙y x y (¬ x)) ⟩
  x + (x * ¬ x) * y ≈⟨ *-lemma x y ⟩
  x                 ∎
  where open CommutativeMonoidProperties *-commutativeMonoid

*-absorbs-∨ : _*_ Absorbs _∨_
*-absorbs-∨ x y = begin
  x * (x ∨ y)           ≈⟨ distribˡ x x (y * ¬ x) ⟩
  x * x + x * (y * ¬ x) ≈⟨ +-cong (*-idem x) (x∙yz≈xz∙y x y (¬ x)) ⟩
  x + (x * ¬ x) * y     ≈⟨ *-lemma x y ⟩
  x                     ∎
  where open CommutativeMonoidProperties *-commutativeMonoid

*-distribʳ-∨ : _*_ DistributesOverʳ _∨_
*-distribʳ-∨ x y z = begin
  (y ∨ z) * x ≈⟨ *-congʳ (∨-def y z) ⟩
  (y + z + y * z) * x ≈⟨ distribʳ x (y + z) (y * z) ⟩
  ((y + z) * x + y * z * x) ≈⟨ +-cong (distribʳ x y z) (∙-distrʳ-∙ x y z) ⟩
  (y * x + z * x) + (y * x) * (z * x)  ≈⟨ ∨-def (y * x) (z * x) ⟨
  (y * x) ∨ (z * x) ∎
  where open IdempotentCommutativeMonoidProperties *-idempotentCommutativeMonoid

-- Structures

∨-isMagma : IsMagma _∨_
∨-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∨-cong }

∨-isSemigroup : IsSemigroup _∨_
∨-isSemigroup = record { isMagma = ∨-isMagma ; assoc = ∨-assoc }

∨-isBand : IsBand _∨_
∨-isBand = record { isSemigroup = ∨-isSemigroup ; idem = ∨-idem }

*-∨-isLattice : IsLattice _*_ _∨_
*-∨-isLattice = isLattice₂ $ record
  { isJoinSemilattice = record { isBand = *-isBand ; comm = *-comm }
  ; isMeetSemilattice = record { isBand = ∨-isBand ; comm = ∨-comm }
  ; absorptive = *-absorbs-∨ , ∨-absorbs-*
  }

*-∨-isDistributiveLattice : IsDistributiveLattice _*_ _∨_
*-∨-isDistributiveLattice = isDistributiveLatticeʳʲᵐ $ record
  { isLattice = *-∨-isLattice
  ; ∨-distribʳ-∧ = *-distribʳ-∨
  }

*-∨-distributiveLattice : DistributiveLattice _ _
*-∨-distributiveLattice = record { isDistributiveLattice = *-∨-isDistributiveLattice }

isDistributiveLattice : IsDistributiveLattice _∨_ _*_
isDistributiveLattice =
  DistributiveLatticeProperties.∧-∨-isDistributiveLattice *-∨-distributiveLattice

isBooleanAlgebra : IsBooleanAlgebra _∨_ _*_ ¬_ 1# 0#
isBooleanAlgebra = isBooleanAlgebraʳ $ record
  { isDistributiveLattice = isDistributiveLattice
  ; ∨-complementʳ = ∨-complementʳ
  ; ∧-complementʳ = ∧-complementʳ
  ; ¬-cong = ¬-cong
  }

-- Bundle

booleanAlgebra : BooleanAlgebra _ _
booleanAlgebra = record { isBooleanAlgebra = isBooleanAlgebra }

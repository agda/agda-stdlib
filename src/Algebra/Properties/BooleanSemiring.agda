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
  using (BooleanAlgebra)
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_)

open BooleanSemiring booleanSemiring
open import Algebra.Consequences.Setoid setoid using (binomial-expansion)
open import Algebra.Definitions _≈_
open import Algebra.Lattice.Structures.Biased _≈_
  using (IsLattice₂; isLattice₂
        ; IsDistributiveLatticeʳʲᵐ; isDistributiveLatticeʳʲᵐ
        ; IsBooleanAlgebraʳ; isBooleanAlgebraʳ
        )
open import Algebra.Lattice.Structures _≈_
  using (IsLattice; IsDistributiveLattice; IsBooleanAlgebra)
open import Algebra.Structures _≈_
  using (IsCommutativeMonoid; IsIdempotentCommutativeMonoid
        ; IsGroup; IsAbelianGroup
        ; IsRing; IsCommutativeRing; IsBooleanRing
        )
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of additive submonoid

open import Algebra.Properties.CommutativeMonoid +-commutativeMonoid public

------------------------------------------------------------------------
-- Extra properties of Boolean semirings

xy+yx≈0 : ∀ x y → x * y + y * x ≈ 0#
xy+yx≈0 x y = +-cancelˡ (x * x) _ _ $ +-cancelʳ (y * y) _ _ $ begin
  x * x + ((x * y) + (y * x)) + y * y ≈⟨ +-congʳ (+-assoc _ _ _) ⟨
  x * x + x * y + y * x + y * y       ≈⟨ expand x y x y ⟨
  (x + y) * (x + y)                   ≈⟨ *-idem (x + y) ⟩
  x + y                               ≈⟨ +-congˡ (*-idem y) ⟨
  x + y * y                           ≈⟨ +-congʳ (*-idem x) ⟨
  x * x + y * y                       ≈⟨ +-congʳ (+-identityʳ (x * x)) ⟨
  x * x + 0# + y * y                  ∎
  where expand = binomial-expansion +-cong +-assoc distrib

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

infixr 6 _∨_
_∨_ : Op₂ Carrier
x ∨ y = x + y + x * y

-- Properties

∨-absorbs-* : _∨_ Absorbs _*_
∨-absorbs-* = {!!}

*-absorbs-∨ : _*_ Absorbs _∨_
*-absorbs-∨ = {!!}

absorptive : Absorptive _∨_ _*_
absorptive = ∨-absorbs-* , *-absorbs-∨

∨-distribʳ-∧ : _∨_ DistributesOverʳ _*_
∨-distribʳ-∧ = {!!}

∧-complementʳ : RightInverse 0# ¬_ _*_
∧-complementʳ x = begin
  x * (¬ x)      ≈⟨ distribˡ x 1# x ⟩
  x * 1# + x * x ≈⟨ +-cong (*-identityʳ x) (*-idem x) ⟩
  x + x          ≈⟨ x+x≈0 x ⟩
  0#             ∎

∨-complementʳ : RightInverse 1# ¬_ _∨_
∨-complementʳ x = begin
  x ∨ ¬ x           ≈⟨ +-cong (x∙yz≈y∙xz x 1# x) (∧-complementʳ x) ⟩
  1# + (x + x) + 0# ≈⟨ +-identityʳ _ ⟩
  1# + (x + x)      ≈⟨ +-congˡ (x+x≈0 x) ⟩
  1# + 0#           ≈⟨ +-identityʳ _ ⟩
  1#                ∎

-- Structures

isLattice : IsLattice _∨_ _*_
isLattice = isLattice₂ $ record
  { isJoinSemilattice = {!!}
  ; isMeetSemilattice = {!!}
  ; absorptive = absorptive
  }

isDistributiveLattice : IsDistributiveLattice _∨_ _*_
isDistributiveLattice = isDistributiveLatticeʳʲᵐ $ record
  { isLattice = isLattice
  ; ∨-distribʳ-∧ = ∨-distribʳ-∧
  }

isBooleanAlgebra : IsBooleanAlgebra _∨_ _*_ ¬_ 1# 0#
isBooleanAlgebra = isBooleanAlgebraʳ $ record
  { isDistributiveLattice = isDistributiveLattice
  ; ∨-complementʳ = ∨-complementʳ
  ; ∧-complementʳ = ∧-complementʳ
  ; ¬-cong = +-congˡ
  }

-- Bundle

booleanAlgebra : BooleanAlgebra _ _
booleanAlgebra = record { isBooleanAlgebra = isBooleanAlgebra }

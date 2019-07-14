------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra where

open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Function
open import Level

------------------------------------------------------------------------
-- Packages with 1 binary operation
------------------------------------------------------------------------

record RawMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier


record Magma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isMagma : IsMagma _≈_ _∙_

  open IsMagma isMagma public

  rawMagma : RawMagma _ _
  rawMagma = record { _≈_ = _≈_; _∙_ = _∙_ }


record Semigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _≈_ _∙_

  open IsSemigroup isSemigroup public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public using (rawMagma)


record Band c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isBand  : IsBand _≈_ _∙_

  open IsBand isBand public

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma; rawMagma)


record Semilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _∧_           : Op₂ Carrier
    isSemilattice : IsSemilattice _≈_ _∧_

  open IsSemilattice isSemilattice public

  band : Band c ℓ
  band = record { isBand = isBand }

  open Band band public using (rawMagma; magma; semigroup)


record SelectiveMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    _∙_              : Op₂ Carrier
    isSelectiveMagma : IsSelectiveMagma _≈_ _∙_

  open IsSelectiveMagma isSelectiveMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public using (rawMagma)

------------------------------------------------------------------------
-- Packages with 1 binary operation & 1 element
------------------------------------------------------------------------

-- A raw monoid is a monoid without any laws.

record RawMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier

  rawMagma : RawMagma c ℓ
  rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    }


record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≈_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup _ _
  semigroup = record { isSemigroup = isSemigroup }

  rawMonoid : RawMonoid _ _
  rawMonoid = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε}

  open Semigroup semigroup public using (rawMagma; magma)


record CommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ
    _∙_                 : Op₂ Carrier
    ε                   : Carrier
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (rawMagma; magma; semigroup; rawMonoid)


record IdempotentCommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier                       : Set c
    _≈_                           : Rel Carrier ℓ
    _∙_                           : Op₂ Carrier
    ε                             : Carrier
    isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _≈_ _∙_ ε

  open IsIdempotentCommutativeMonoid isIdempotentCommutativeMonoid public

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (rawMagma; magma; semigroup; rawMonoid; monoid)


-- Idempotent commutative monoids are also known as bounded lattices.
-- Note that the BoundedLattice necessarily uses the notation inherited
-- from monoids rather than lattices.

BoundedLattice = IdempotentCommutativeMonoid

module BoundedLattice {c ℓ} (idemCommMonoid : IdempotentCommutativeMonoid c ℓ) =
       IdempotentCommutativeMonoid idemCommMonoid


------------------------------------------------------------------------
-- Packages with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record RawGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier

  rawMonoid : RawMonoid c ℓ
  rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε   = ε
    }

  open RawMonoid rawMonoid public
    using (rawMagma)


record Group c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isGroup : IsGroup _≈_ _∙_ ε _⁻¹

  open IsGroup isGroup public

  rawGroup : RawGroup _ _
  rawGroup = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε; _⁻¹ = _⁻¹}

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (rawMagma; magma; semigroup; rawMonoid)


record AbelianGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _∙_            : Op₂ Carrier
    ε              : Carrier
    _⁻¹            : Op₁ Carrier
    isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group _ _
  group = record { isGroup = isGroup }

  open Group group public
    using (rawMagma; magma; semigroup; monoid; rawMonoid; rawGroup)

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid =
    record { isCommutativeMonoid = isCommutativeMonoid }


------------------------------------------------------------------------
-- Packages with 2 binary operations
------------------------------------------------------------------------

record Lattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ
    _∨_       : Op₂ Carrier
    _∧_       : Op₂ Carrier
    isLattice : IsLattice _≈_ _∨_ _∧_

  open IsLattice isLattice public

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }


record DistributiveLattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _∨_                   : Op₂ Carrier
    _∧_                   : Op₂ Carrier
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice _ _
  lattice = record { isLattice = isLattice }

  open Lattice lattice public using (setoid)


------------------------------------------------------------------------
-- Packages with 2 binary operations & 1 element
------------------------------------------------------------------------

record NearSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    0#             : Carrier
    isNearSemiring : IsNearSemiring _≈_ _+_ _*_ 0#

  open IsNearSemiring isNearSemiring public

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using ()
    renaming
    ( rawMagma  to +-rawMagma
    ; magma     to +-magma
    ; semigroup to +-semigroup
    ; rawMonoid to +-rawMonoid
    )

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open Semigroup *-semigroup public
    using ()
    renaming
    ( rawMagma to *-rawMagma
    ; magma    to *-magma
    )


record SemiringWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ
    _+_                  : Op₂ Carrier
    _*_                  : Op₂ Carrier
    0#                   : Carrier
    isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsSemiringWithoutOne isSemiringWithoutOne public

  nearSemiring : NearSemiring _ _
  nearSemiring = record { isNearSemiring = isNearSemiring }

  open NearSemiring nearSemiring public
    using
    ( +-rawMagma; +-magma; +-semigroup; +-rawMonoid; +-monoid
    ; *-rawMagma; *-magma; *-semigroup
    )

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }


record CommutativeSemiringWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                         : Set c
    _≈_                             : Rel Carrier ℓ
    _+_                             : Op₂ Carrier
    _*_                             : Op₂ Carrier
    0#                              : Carrier
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsCommutativeSemiringWithoutOne
         isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; nearSemiring
    )

------------------------------------------------------------------------
-- Packages with 2 binary operations & 2 elements
------------------------------------------------------------------------

record RawSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier


record SemiringWithoutAnnihilatingZero c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                           : Set c
    _≈_                               : Rel Carrier ℓ
    _+_                               : Op₂ Carrier
    _*_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using ()
    renaming
    ( rawMagma  to +-rawMagma
    ; magma     to +-magma
    ; semigroup to +-semigroup
    ; rawMonoid to +-rawMonoid
    ; monoid    to +-monoid
    )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using ()
    renaming
    ( rawMagma  to *-rawMagma
    ; magma     to *-magma
    ; semigroup to *-semigroup
    ; rawMonoid to *-rawMonoid
    )


record Semiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#

  open IsSemiring isSemiring public

  rawSemiring : RawSemiring _ _
  rawSemiring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
    using
    ( +-rawMagma;  +-magma;  +-semigroup
    ; *-rawMagma;  *-magma;  *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    )

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using (nearSemiring)


record CommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#

  open IsCommutativeSemiring isCommutativeSemiring public

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    ; rawSemiring
    )

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid =
    record { isCommutativeMonoid = *-isCommutativeMonoid }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }


------------------------------------------------------------------------
-- Packages with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

-- A raw ring is a ring without any laws.

record RawRing c : Set (suc c) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier : Set c
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier


record Ring c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isRing  : IsRing _≈_ _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid ; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group)

  rawRing : RawRing _
  rawRing = record
    { _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }


record CommutativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    -_                : Op₁ Carrier
    0#                : Carrier
    1#                : Carrier
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring _ _
  ring = record { isRing = isRing }

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open Ring ring public using (rawRing; +-group; +-abelianGroup)
  open CommutativeSemiring commutativeSemiring public
    using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne
    )


record BooleanAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    _∨_              : Op₂ Carrier
    _∧_              : Op₂ Carrier
    ¬_               : Op₁ Carrier
    ⊤                : Carrier
    ⊥                : Carrier
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice _ _
  distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
    using (setoid; lattice)



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

RawSemigroup = RawMagma
{-# WARNING_ON_USAGE RawSemigroup
"Warning: RawSemigroup was deprecated in v1.0.
Please use RawMagma instead."
#-}

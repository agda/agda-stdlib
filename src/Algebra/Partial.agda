------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like monoids and rings
-- (packed in records with their operations, etc)
-- The reason the carrier type is parameterized is to make notions of
-- submonoids/subgroups/etc. possible.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Partial where

open import Relation.Binary
open import Relation.Binary.Partial
open import Algebra.Partial.FunctionProperties
open import Algebra.Partial.Structures
open import Level

record RawMagma {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A

record Magma {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    isMagma : IsMagma _≈_ _∙_

  open IsMagma isMagma public

  rawMagma : RawMagma _ _
  rawMagma = record { _≈_ = _≈_; _∙_ = _∙_ }

record Semigroup {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    isSemigroup : IsSemigroup _≈_ _∙_

  open IsSemigroup isSemigroup public

  magma : Magma ℓ A
  magma = record { isMagma = isMagma }

  open Magma magma public using (rawMagma)

record Band {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    isBand  : IsBand _≈_ _∙_

  open IsBand isBand public

  semigroup : Semigroup ℓ A
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma; rawMagma)

record Semilattice {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infix  4 _≈_
  field
    _≈_           : Rel A ℓ
    _∧_           : Op₂ A
    isSemilattice : IsSemilattice _≈_ _∧_

  open IsSemilattice isSemilattice public

  band : Band ℓ A
  band = record { isBand = isBand }

  open Band band public using (rawMagma; magma; semigroup)

record SelectiveMagma {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_              : Rel A ℓ
    _∙_              : Op₂ A
    isSelectiveMagma : IsSelectiveMagma _≈_ _∙_

  open IsSelectiveMagma isSelectiveMagma public

  magma : Magma ℓ A
  magma = record { isMagma = isMagma }

  open Magma magma public using (rawMagma)

------------------------------------------------------------------------
-- Packages with 1 binary operation & 1 element
------------------------------------------------------------------------

-- A raw monoid is a monoid without any laws.

record RawMonoid {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    ε       : A

record Monoid {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_      : Rel A ℓ
    _∙_      : Op₂ A
    ε        : A
    isMonoid : IsMonoid _≈_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup _ _
  semigroup = record { isSemigroup = isSemigroup }

  rawMonoid : RawMonoid _ _
  rawMonoid = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε}

  open Semigroup semigroup public using (rawMagma; magma)

record CommutativeMonoid {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_                 : Rel A ℓ
    _∙_                 : Op₂ A
    ε                   : A
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (rawMagma; magma; semigroup; rawMonoid)

record IdempotentCommutativeMonoid {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_                           : Rel A ℓ
    _∙_                           : Op₂ A
    ε                             : A
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

module BoundedLattice {c ℓ A}  (idemCommMonoid : IdempotentCommutativeMonoid {c} ℓ A) =
       IdempotentCommutativeMonoid idemCommMonoid

------------------------------------------------------------------------
-- Packages with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record RawGroup {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    ε       : A
    _⁻¹     : Op₁ A


record Group {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _∙_     : Op₂ A
    ε       : A
    _⁻¹     : Op₁ A
    isGroup : IsGroup _≈_ _∙_ ε _⁻¹

  open IsGroup isGroup public

  rawGroup : RawGroup _ _
  rawGroup = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε; _⁻¹ = _⁻¹}

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (rawMagma; magma; semigroup; rawMonoid)

record AbelianGroup {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_            : Rel A ℓ
    _∙_            : Op₂ A
    ε              : A
    _⁻¹            : Op₁ A
    isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group _ _
  group = record { isGroup = isGroup }

  open Group group public
    using (rawMagma; magma; semigroup; monoid; rawMonoid; rawGroup)

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid =
    record { isCommutativeMonoid = isCommutativeMonoid }

record Lattice {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    _≈_       : Rel A ℓ
    _∨_       : Op₂ A
    _∧_       : Op₂ A
    isLattice : IsLattice _≈_ _∨_ _∧_

  open IsLattice isLattice public

  partialSetoid : PartialSetoid A ℓ
  partialSetoid = record { isPartialEquivalence = isPartialEquivalence }

record DistributiveLattice {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    _≈_                   : Rel A ℓ
    _∨_                   : Op₂ A
    _∧_                   : Op₂ A
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice _ _
  lattice = record { isLattice = isLattice }

  open Lattice lattice public using (partialSetoid)


------------------------------------------------------------------------
-- Packages with 2 binary operations & 1 element
------------------------------------------------------------------------

record NearSemiring {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_            : Rel A ℓ
    _+_            : Op₂ A
    _*_            : Op₂ A
    0#             : A
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

record SemiringWithoutOne {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_                  : Rel A ℓ
    _+_                  : Op₂ A
    _*_                  : Op₂ A
    0#                   : A
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


record CommutativeSemiringWithoutOne {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_                             : Rel A ℓ
    _+_                             : Op₂ A
    _*_                             : Op₂ A
    0#                              : A
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

record RawSemiring {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_        : Rel A ℓ
    _+_        : Op₂ A
    _*_        : Op₂ A
    0#         : A
    1#         : A

record SemiringWithoutAnnihilatingZero {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_                               : Rel A ℓ
    _+_                               : Op₂ A
    _*_                               : Op₂ A
    0#                                : A
    1#                                : A
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

record Semiring {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_        : Rel A ℓ
    _+_        : Op₂ A
    _*_        : Op₂ A
    0#         : A
    1#         : A
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


record CommutativeSemiring {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_                   : Rel A ℓ
    _+_                   : Op₂ A
    _*_                   : Op₂ A
    0#                    : A
    1#                    : A
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

record RawRing {c} (A : Set c) : Set (suc c) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    _+_     : Op₂ A
    _*_     : Op₂ A
    -_      : Op₁ A
    0#      : A
    1#      : A


record Ring {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_     : Rel A ℓ
    _+_     : Op₂ A
    _*_     : Op₂ A
    -_      : Op₁ A
    0#      : A
    1#      : A
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


record CommutativeRing {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    _≈_               : Rel A ℓ
    _+_               : Op₂ A
    _*_               : Op₂ A
    -_                : Op₁ A
    0#                : A
    1#                : A
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


record BooleanAlgebra {c} ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    _≈_              : Rel A ℓ
    _∨_              : Op₂ A
    _∧_              : Op₂ A
    ¬_               : Op₁ A
    ⊤                : A
    ⊥                : A
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice _ _
  distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
    using (partialSetoid; lattice)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`.

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles where

import Algebra.Bundles.Raw as Raw
open import Algebra.Core
open import Algebra.Structures
open import Relation.Binary
open import Function.Base
import Relation.Nullary as N
open import Level

------------------------------------------------------------------------
-- Re-export definitions of 'raw' bundles

open Raw public
  using (RawMagma; RawMonoid; RawGroup
        ; RawNearSemiring; RawSemiring
        ; RawRingWithoutOne; RawRing
        ; RawQuasigroup; RawLoop)

------------------------------------------------------------------------
-- Bundles with 1 binary operation
------------------------------------------------------------------------

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

  open RawMagma rawMagma public
    using (_≉_)


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


record CommutativeMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ
    _∙_                : Op₂ Carrier
    isCommutativeMagma : IsCommutativeMagma _≈_ _∙_

  open IsCommutativeMagma isCommutativeMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public using (rawMagma)

record IdempotentMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isIdempotentMagma  : IsIdempotentMagma _≈_ _∙_

  open IsIdempotentMagma isIdempotentMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record AlternativeMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isAlternativeMagma  : IsAlternativeMagma _≈_ _∙_

  open IsAlternativeMagma isAlternativeMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record FlexibleMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isFlexibleMagma  : IsFlexibleMagma _≈_ _∙_

  open IsFlexibleMagma isFlexibleMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record MedialMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isMedialMagma  : IsMedialMagma _≈_ _∙_

  open IsMedialMagma isMedialMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record SemimedialMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isSemimedialMagma  : IsSemimedialMagma _≈_ _∙_

  open IsSemimedialMagma isSemimedialMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)


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

  open Magma magma public
    using (_≉_; rawMagma)


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

  open Semigroup semigroup public
    using (_≉_; magma; rawMagma)


record CommutativeSemigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier                 : Set c
    _≈_                     : Rel Carrier ℓ
    _∙_                     : Op₂ Carrier
    isCommutativeSemigroup  : IsCommutativeSemigroup _≈_ _∙_

  open IsCommutativeSemigroup isCommutativeSemigroup public

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public
    using (_≉_; magma; rawMagma)

  commutativeMagma : CommutativeMagma c ℓ
  commutativeMagma = record { isCommutativeMagma = isCommutativeMagma }

------------------------------------------------------------------------
-- Bundles with 1 binary operation & 1 element
------------------------------------------------------------------------

record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isUnitalMagma : IsUnitalMagma _≈_ _∙_ ε

  open IsUnitalMagma isUnitalMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; rawMagma)


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

  open Semigroup semigroup public
    using (_≉_; rawMagma; magma)

  rawMonoid : RawMonoid _ _
  rawMonoid = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε}

  unitalMagma : UnitalMagma _ _
  unitalMagma = record { isUnitalMagma = isUnitalMagma  }


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

  open Monoid monoid public
    using (_≉_; rawMagma; magma; semigroup; unitalMagma; rawMonoid)

  commutativeSemigroup : CommutativeSemigroup _ _
  commutativeSemigroup = record { isCommutativeSemigroup = isCommutativeSemigroup }

  open CommutativeSemigroup commutativeSemigroup public
    using (commutativeMagma)


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
    using
    ( _≉_; rawMagma; magma; unitalMagma; commutativeMagma
    ; semigroup; commutativeSemigroup
    ; rawMonoid; monoid
    )


-- Idempotent commutative monoids are also known as bounded lattices.
-- Note that the BoundedLattice necessarily uses the notation inherited
-- from monoids rather than lattices.

BoundedLattice = IdempotentCommutativeMonoid

module BoundedLattice {c ℓ} (idemCommMonoid : IdempotentCommutativeMonoid c ℓ) =
       IdempotentCommutativeMonoid idemCommMonoid


------------------------------------------------------------------------
-- Bundles with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record InvertibleMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isInvertibleMagma : IsInvertibleMagma _≈_ _∙_ ε _⁻¹

  open IsInvertibleMagma isInvertibleMagma public

  magma : Magma _ _
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; rawMagma)


record InvertibleUnitalMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ
    _∙_                      : Op₂ Carrier
    ε                        : Carrier
    _⁻¹                      : Op₁ Carrier
    isInvertibleUnitalMagma  : IsInvertibleUnitalMagma _≈_ _∙_ ε _⁻¹

  open IsInvertibleUnitalMagma isInvertibleUnitalMagma public

  invertibleMagma : InvertibleMagma _ _
  invertibleMagma = record { isInvertibleMagma = isInvertibleMagma }

  open InvertibleMagma invertibleMagma public
    using (_≉_; rawMagma; magma)

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

  open Monoid monoid public
    using (_≉_; rawMagma; magma; semigroup; unitalMagma; rawMonoid)

  invertibleMagma : InvertibleMagma c ℓ
  invertibleMagma = record
    { isInvertibleMagma = isInvertibleMagma
    }

  invertibleUnitalMagma : InvertibleUnitalMagma c ℓ
  invertibleUnitalMagma = record
    { isInvertibleUnitalMagma = isInvertibleUnitalMagma
    }

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

  open Group group public using
    (_≉_; rawMagma; magma; semigroup
    ; rawMonoid; monoid; rawGroup; invertibleMagma; invertibleUnitalMagma
    )

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (commutativeMagma; commutativeSemigroup)

------------------------------------------------------------------------
-- Bundles with 2 binary operations & 1 element
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

  rawNearSemiring : RawNearSemiring _ _
  rawNearSemiring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0#  = 0#
    }

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using (_≉_) renaming
    ( rawMagma    to  +-rawMagma
    ; magma       to  +-magma
    ; semigroup   to  +-semigroup
    ; unitalMagma to  +-unitalMagma
    ; rawMonoid   to  +-rawMonoid
    )

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open Semigroup *-semigroup public
    using () renaming
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
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-semigroup
    ; +-rawMonoid; +-monoid
    ; *-rawMagma; *-magma; *-semigroup
    ; rawNearSemiring
    )

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid = record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using () renaming
    ( commutativeMagma     to +-commutativeMagma
    ; commutativeSemigroup to +-commutativeSemigroup
    )


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
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; nearSemiring; rawNearSemiring
    )

------------------------------------------------------------------------
-- Bundles with 2 binary operations & 2 elements
------------------------------------------------------------------------

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

  rawSemiring : RawSemiring c ℓ
  rawSemiring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  open RawSemiring rawSemiring public
    using (rawNearSemiring)

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using (_≉_) renaming
    ( rawMagma             to +-rawMagma
    ; magma                to +-magma
    ; unitalMagma          to +-unitalMagma
    ; commutativeMagma     to +-commutativeMagma
    ; semigroup            to +-semigroup
    ; commutativeSemigroup to +-commutativeSemigroup
    ; rawMonoid            to +-rawMonoid
    ; monoid               to +-monoid
    )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using () renaming
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

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
    using
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma;  *-magma;  *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; rawNearSemiring ; rawSemiring
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
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    ; rawSemiring
    )

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid = record
    { isCommutativeMonoid = *-isCommutativeMonoid
    }

  open CommutativeMonoid *-commutativeMonoid public
    using () renaming
    ( commutativeMagma     to *-commutativeMagma
    ; commutativeSemigroup to *-commutativeSemigroup
    )

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }


record CancellativeCommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
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
    isCancellativeCommutativeSemiring : IsCancellativeCommutativeSemiring _≈_ _+_ _*_ 0# 1#

  open IsCancellativeCommutativeSemiring isCancellativeCommutativeSemiring public

  commutativeSemiring : CommutativeSemiring c ℓ
  commutativeSemiring = record
    { isCommutativeSemiring = isCommutativeSemiring
    }

  open CommutativeSemiring commutativeSemiring public
    using
    ( +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-commutativeMagma; *-semigroup; *-commutativeSemigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    ; rawSemiring
    ; semiring
    ; _≉_
    )

record IdempotentSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                : Set c
    _≈_                    : Rel Carrier ℓ
    _+_                    : Op₂ Carrier
    _*_                    : Op₂ Carrier
    0#                     : Carrier
    1#                     : Carrier
    isIdempotentSemiring   : IsIdempotentSemiring _≈_ _+_ _*_ 0# 1#

  open IsIdempotentSemiring isIdempotentSemiring public

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    ; rawSemiring
    )

record KleeneAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⋆
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    _⋆                    : Op₁ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isKleeneAlgebra       : IsKleeneAlgebra _≈_ _+_ _*_ _⋆ 0# 1#

  open IsKleeneAlgebra isKleeneAlgebra public

  idempotentSemiring : IdempotentSemiring _ _
  idempotentSemiring = record { isIdempotentSemiring = isIdempotentSemiring }

  open IdempotentSemiring idempotentSemiring public
    using
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    ; rawSemiring; semiring
    )

record Quasiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isQuasiring   : IsQuasiring _≈_ _+_ _*_ 0# 1#

  open IsQuasiring isQuasiring public

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using (_≉_) renaming
    ( rawMagma    to  +-rawMagma
    ; magma       to  +-magma
    ; semigroup   to  +-semigroup
    ; unitalMagma to  +-unitalMagma
    ; rawMonoid   to  +-rawMonoid
    )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using () renaming
    ( rawMagma  to *-rawMagma
    ; magma     to *-magma
    ; semigroup to *-semigroup
    ; rawMonoid to *-rawMonoid
    )

------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record RingWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
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
    isRingWithoutOne  : IsRingWithoutOne _≈_ _+_ _*_ -_ 0#

  open IsRingWithoutOne isRingWithoutOne public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group; invertibleMagma to +-invertibleMagma; invertibleUnitalMagma to +-invertibleUnitalMagma)

  open Semigroup *-semigroup public
    using () renaming
    ( rawMagma to *-rawMagma
    ; magma    to *-magma
    )

------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record NonAssociativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    -_                    : Op₁ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isNonAssociativeRing  : IsNonAssociativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsNonAssociativeRing isNonAssociativeRing public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group; invertibleMagma to +-invertibleMagma; invertibleUnitalMagma to +-invertibleUnitalMagma)

record Nearring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    -_            : Op₁ Carrier
    0#            : Carrier
    1#            : Carrier
    isNearring    : IsNearring _≈_ _+_ _*_ 0# 1# -_

  open IsNearring isNearring public

  quasiring : Quasiring _ _
  quasiring = record { isQuasiring = isQuasiring }

  open Quasiring quasiring public
    using
    (_≉_; +-rawMagma; +-magma; +-unitalMagma; +-semigroup; +-monoid; +-rawMonoid
    ;*-rawMagma; *-magma; *-semigroup; *-monoid
    )


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
    ( _≉_; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid ; +-commutativeMonoid
    ; *-rawMonoid; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group; invertibleMagma to +-invertibleMagma; invertibleUnitalMagma to +-invertibleUnitalMagma)

  rawRing : RawRing _ _
  rawRing = record
    { _≈_ = _≈_
    ; _+_ = _+_
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

  open Ring ring public using (_≉_; rawRing; +-invertibleMagma; +-invertibleUnitalMagma; +-group; +-abelianGroup)

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open CommutativeSemiring commutativeSemiring public
    using
    ( +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-commutativeMagma; *-semigroup; *-commutativeSemigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne
    )

------------------------------------------------------------------------
-- Bundles with 3 binary operations
------------------------------------------------------------------------

record Quasigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier      : Set c
    _≈_          : Rel Carrier ℓ
    _∙_          : Op₂ Carrier
    _\\_         : Op₂ Carrier
    _//_         : Op₂ Carrier
    isQuasigroup : IsQuasigroup  _≈_ _∙_ _\\_ _//_

  open IsQuasigroup isQuasigroup public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; rawMagma)

  rawQuasigroup : RawQuasigroup c ℓ
  rawQuasigroup = record
    { _≈_  = _≈_
    ; _∙_  = _∙_
    ; _\\_  = _\\_
    ; _//_  = _//_
    }

  open RawQuasigroup rawQuasigroup public
    using (//-rawMagma; \\-rawMagma; ∙-rawMagma)

record Loop  c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isLoop  : IsLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsLoop isLoop public

  rawLoop : RawLoop c ℓ
  rawLoop = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; _\\_ = _\\_
    ; _//_ = _//_
    ; ε = ε
    }

  quasigroup : Quasigroup _ _
  quasigroup = record { isQuasigroup = isQuasigroup }

  open Quasigroup quasigroup public
    using (_≉_; ∙-rawMagma; \\-rawMagma; //-rawMagma)

record LeftBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isLeftBolLoop : IsLeftBolLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsLeftBolLoop isLeftBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)

record RightBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isRightBolLoop : IsRightBolLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsRightBolLoop isRightBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)

record MoufangLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isMoufangLoop : IsMoufangLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsMoufangLoop isMoufangLoop public

  leftBolLoop : LeftBolLoop _ _
  leftBolLoop = record { isLeftBolLoop = isLeftBolLoop }

  open LeftBolLoop leftBolLoop public
    using (loop)

record MiddleBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ
    _∙_             : Op₂ Carrier
    _\\_            : Op₂ Carrier
    _//_            : Op₂ Carrier
    ε               : Carrier
    isMiddleBolLoop : IsMiddleBolLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsMiddleBolLoop isMiddleBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'raw' bundles
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles.Raw where

open import Algebra.Core
open import Relation.Binary.Core using (Rel)
open import Level using (suc; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)

------------------------------------------------------------------------
-- Raw bundles with 1 binary operation
------------------------------------------------------------------------

record RawMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier

  infix 4 _≉_
  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

------------------------------------------------------------------------
-- Raw bundles with 1 binary operation & 1 element
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

  open RawMagma rawMagma public
    using (_≉_)

------------------------------------------------------------------------
-- Raw bundles with 1 binary operation, 1 unary operation & 1 element
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
    using (_≉_; rawMagma)

------------------------------------------------------------------------
-- Raw bundles with 2 binary operations & 1 element
------------------------------------------------------------------------

record RawNearSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    0#      : Carrier

  +-rawMonoid : RawMonoid c ℓ
  +-rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _+_
    ;  ε  = 0#
    }

  open RawMonoid +-rawMonoid public
    using (_≉_) renaming (rawMagma to +-rawMagma)

  *-rawMagma : RawMagma c ℓ
  *-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _*_
    }

------------------------------------------------------------------------
-- Raw bundles with 2 binary operations & 2 elements
------------------------------------------------------------------------

record RawSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    0#      : Carrier
    1#      : Carrier

  rawNearSemiring : RawNearSemiring c ℓ
  rawNearSemiring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0#  = 0#
    }

  open RawNearSemiring rawNearSemiring public
    using (_≉_; +-rawMonoid; +-rawMagma; *-rawMagma)

  *-rawMonoid : RawMonoid c ℓ
  *-rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _*_
    ; ε   = 1#
    }

------------------------------------------------------------------------
-- Raw bundles with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record RawRingWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
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

  +-rawGroup : RawGroup c ℓ
  +-rawGroup = record
    { _≈_ = _≈_
    ; _∙_ = _+_
    ; ε   = 0#
    ; _⁻¹ = -_
    }

  open RawGroup +-rawGroup public
    using (_≉_) renaming (rawMagma to +-rawMagma; rawMonoid to +-rawMonoid)

  *-rawMagma : RawMagma c ℓ
  *-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _*_
    }

------------------------------------------------------------------------
-- Raw bundles with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

-- A raw ring is a ring without any laws.

record RawRing c ℓ : Set (suc (c ⊔ ℓ)) where
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

  rawSemiring : RawSemiring c ℓ
  rawSemiring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  open RawSemiring rawSemiring public
    using
    ( _≉_
    ; +-rawMagma; +-rawMonoid
    ; *-rawMagma; *-rawMonoid
    )

  +-rawGroup : RawGroup c ℓ
  +-rawGroup = record
    { _≈_ = _≈_
    ; _∙_ = _+_
    ; ε   = 0#
    ; _⁻¹ = -_
    }

------------------------------------------------------------------------
-- Raw bundles with 3 binary operations
------------------------------------------------------------------------

record RawQuasigroup c ℓ : Set (suc (c ⊔ ℓ)) where
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

  ∙-rawMagma : RawMagma c ℓ
  ∙-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    }

  \\-rawMagma : RawMagma c ℓ
  \\-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _\\_
    }

  //-rawMagma : RawMagma c ℓ
  //-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _//_
    }

  open RawMagma \\-rawMagma public
    using (_≉_)

------------------------------------------------------------------------
-- Raw bundles with 3 binary operations & 1 element
------------------------------------------------------------------------

record RawLoop  c ℓ : Set (suc (c ⊔ ℓ)) where
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

  rawQuasigroup : RawQuasigroup c ℓ
  rawQuasigroup = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; _\\_ = _\\_
    ; _//_ = _//_
    }

  open RawQuasigroup rawQuasigroup public
    using (_≉_ ; ∙-rawMagma; \\-rawMagma; //-rawMagma)

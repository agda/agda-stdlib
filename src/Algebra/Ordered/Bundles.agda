------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of ordered algebraic structures like promonoids and
-- posemigroups (packed in records together with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Order`.

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Ordered.Bundles where

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Ordered.Structures
open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Bundles using (Preorder; Poset)

------------------------------------------------------------------------
-- Bundles of preordered structures

-- Preordered magmas (promagmas)

record Promagma c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_        : Rel Carrier ℓ₂  -- The preorder.
    _∙_        : Op₂ Carrier     -- Multiplication.
    isPromagma : IsPromagma _≈_ _≤_ _∙_

  open IsPromagma isPromagma public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }

  magma : Magma c ℓ₁
  magma = record { isMagma = isMagma }

-- Preordered semigroups (prosemigroups)

record Prosemigroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_            : Rel Carrier ℓ₂  -- The preorder.
    _∙_            : Op₂ Carrier     -- Multiplication.
    isProsemigroup : IsProsemigroup _≈_ _≤_ _∙_

  open IsProsemigroup isProsemigroup public

  promagma : Promagma c ℓ₁ ℓ₂
  promagma = record { isPromagma = isPromagma }

  open Promagma promagma public using (preorder; magma)

  semigroup : Semigroup c ℓ₁
  semigroup = record { isSemigroup = isSemigroup }

-- Preordered monoids (promonoids)

record Promonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_         : Rel Carrier ℓ₂  -- The preorder.
    _∙_         : Op₂ Carrier     -- The monoid multiplication.
    ε           : Carrier         -- The monoid unit.
    isPromonoid : IsPromonoid _≈_ _≤_ _∙_ ε

  open IsPromonoid isPromonoid public

  prosemigroup : Prosemigroup c ℓ₁ ℓ₂
  prosemigroup = record { isProsemigroup = isProsemigroup }

  open Prosemigroup prosemigroup public
    using (preorder; magma; promagma; semigroup)

  monoid : Monoid c ℓ₁
  monoid = record { isMonoid = isMonoid }

-- Preordered commutative monoids (commutative promonoids)

record CommutativePromonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The preorder.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    ε       : Carrier         -- The monoid unit.
    isCommutativePromonoid : IsCommutativePromonoid _≈_ _≤_ _∙_ ε

  open IsCommutativePromonoid isCommutativePromonoid public

  promonoid : Promonoid c ℓ₁ ℓ₂
  promonoid = record { isPromonoid = isPromonoid }

  open Promonoid promonoid public
    using (preorder; magma; promagma; semigroup; prosemigroup; monoid)

  commutativeMonoid : CommutativeMonoid c ℓ₁
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public using (commutativeSemigroup)

-- Preordered semirings (prosemirings)

record Prosemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isProsemiring : IsProsemiring _≈_ _≤_ _+_ _*_ 0# 1#

  open IsProsemiring isProsemiring public

  +-commutativePromonoid : CommutativePromonoid c ℓ₁ ℓ₂
  +-commutativePromonoid = record
    { isCommutativePromonoid = +-isCommutativePromonoid }

  open CommutativePromonoid +-commutativePromonoid public
    using (preorder)
    renaming
    ( magma                to +-magma
    ; promagma             to +-promagma
    ; semigroup            to +-semigroup
    ; prosemigroup         to +-prosemigroup
    ; monoid               to +-monoid
    ; promonoid            to +-promonoid
    ; commutativeSemigroup to +-commutativeSemigroup
    ; commutativeMonoid    to +-commutativeMonoid
    )

  *-promonoid : Promonoid c ℓ₁ ℓ₂
  *-promonoid = record { isPromonoid = *-isPromonoid }

  open Promonoid *-promonoid public
    using ()
    renaming
    ( magma        to *-magma
    ; promagma     to *-promagma
    ; semigroup    to *-semigroup
    ; prosemigroup to *-prosemigroup
    ; monoid       to *-monoid
    )

  semiring : Semiring c ℓ₁
  semiring = record { isSemiring = isSemiring }

-- Preordered IdempotentSemiring (IdempotentProsemiring)

record IdempotentProsemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isIdempotentProsemiring : IsIdempotentProsemiring _≈_ _≤_ _+_ _*_ 0# 1#

  open IsIdempotentProsemiring isIdempotentProsemiring public

  idempotentSemiring : IdempotentSemiring c ℓ₁
  idempotentSemiring = record { isIdempotentSemiring = isIdempotentSemiring }

-- Preordered KleeneAlgebra (proKleeneAlgebra)

record ProKleeneAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infix  8 _⋆
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    _⋆            : Op₁ Carrier
    0#            : Carrier
    1#            : Carrier
    isProKleeneAlgebra : IsProKleeneAlgebra _≈_ _≤_ _+_ _*_ _⋆ 0# 1#

  open IsProKleeneAlgebra isProKleeneAlgebra public

  kleeneAlgebra : KleeneAlgebra c ℓ₁
  kleeneAlgebra = record { isKleeneAlgebra = isKleeneAlgebra }

------------------------------------------------------------------------
-- Bundles of partially ordered structures

-- Partially ordered magmas (pomagmas)

record Pomagma c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_       : Rel Carrier ℓ₂  -- The partial order.
    _∙_       : Op₂ Carrier     -- Multiplication.
    isPomagma : IsPomagma _≈_ _≤_ _∙_

  open IsPomagma isPomagma public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  promagma : Promagma c ℓ₁ ℓ₂
  promagma = record { isPromagma = isPromagma }

  open Promagma promagma public using (preorder; magma)

-- Partially ordered semigroups (posemigroups)

record Posemigroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_           : Rel Carrier ℓ₂  -- The partial order.
    _∙_           : Op₂ Carrier     -- Multiplication.
    isPosemigroup : IsPosemigroup _≈_ _≤_ _∙_

  open IsPosemigroup isPosemigroup public

  pomagma : Pomagma c ℓ₁ ℓ₂
  pomagma = record { isPomagma = isPomagma }

  open Pomagma pomagma public using (preorder; poset; magma; promagma)

  prosemigroup : Prosemigroup c ℓ₁ ℓ₂
  prosemigroup = record { isProsemigroup = isProsemigroup }

  open Prosemigroup prosemigroup public using (semigroup)

-- Partially ordered monoids (pomonoids)

record Pomonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_        : Rel Carrier ℓ₂  -- The partial order.
    _∙_        : Op₂ Carrier     -- The monoid multiplication.
    ε          : Carrier         -- The monoid unit.
    isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε

  open IsPomonoid isPomonoid public

  posemigroup : Posemigroup c ℓ₁ ℓ₂
  posemigroup = record { isPosemigroup = isPosemigroup }

  open Posemigroup posemigroup public using
    ( preorder
    ; poset
    ; magma
    ; promagma
    ; pomagma
    ; semigroup
    ; prosemigroup
    )

  promonoid : Promonoid c ℓ₁ ℓ₂
  promonoid = record { isPromonoid = isPromonoid }

  open Promonoid promonoid public using (monoid)

-- Partially ordered commutative monoids (commutative pomonoids)

record CommutativePomonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                   : Rel Carrier ℓ₂  -- The partial order.
    _∙_                   : Op₂ Carrier     -- The monoid multiplication.
    ε                     : Carrier         -- The monoid unit.
    isCommutativePomonoid : IsCommutativePomonoid _≈_ _≤_ _∙_ ε

  open IsCommutativePomonoid isCommutativePomonoid public

  pomonoid : Pomonoid c ℓ₁ ℓ₂
  pomonoid = record { isPomonoid = isPomonoid }

  open Pomonoid pomonoid public using
    ( preorder
    ; poset
    ; magma
    ; promagma
    ; pomagma
    ; semigroup
    ; prosemigroup
    ; posemigroup
    ; monoid
    ; promonoid
    )

  commutativePromonoid : CommutativePromonoid c ℓ₁ ℓ₂
  commutativePromonoid =
    record { isCommutativePromonoid = isCommutativePromonoid }

  open CommutativePromonoid commutativePromonoid public
    using (commutativeSemigroup; commutativeMonoid)

-- Partially ordered semirings (posemirings)

record Posemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier      : Set c
    _≈_          : Rel Carrier ℓ₁
    _≤_          : Rel Carrier ℓ₂
    _+_          : Op₂ Carrier
    _*_          : Op₂ Carrier
    0#           : Carrier
    1#           : Carrier
    isPosemiring : IsPosemiring _≈_ _≤_ _+_ _*_ 0# 1#

  open IsPosemiring isPosemiring public

  +-commutativePomonoid : CommutativePomonoid c ℓ₁ ℓ₂
  +-commutativePomonoid = record
    { isCommutativePomonoid = +-isCommutativePomonoid }

  open CommutativePomonoid +-commutativePomonoid public
    using (preorder)
    renaming
    ( magma                to +-magma
    ; promagma             to +-promagma
    ; pomagma              to +-pomagma
    ; semigroup            to +-semigroup
    ; prosemigroup         to +-prosemigroup
    ; posemigroup          to +-posemigroup
    ; monoid               to +-monoid
    ; promonoid            to +-promonoid
    ; pomonoid             to +-pomonoid
    ; commutativeSemigroup to +-commutativeSemigroup
    ; commutativeMonoid    to +-commutativeMonoid
    ; commutativePromonoid to +-commutativePromonoid
    )

  *-pomonoid : Pomonoid c ℓ₁ ℓ₂
  *-pomonoid = record { isPomonoid = *-isPomonoid }

  open Pomonoid *-pomonoid public
    using ()
    renaming
    ( magma        to *-magma
    ; promagma     to *-promagma
    ; pomagma      to *-pomagma
    ; semigroup    to *-semigroup
    ; prosemigroup to *-prosemigroup
    ; posemigroup  to *-posemigroup
    ; monoid       to *-monoid
    ; promonoid    to *-promonoid
    )

  prosemiring : Prosemiring c ℓ₁ ℓ₂
  prosemiring = record { isProsemiring = isProsemiring }

  open Prosemiring prosemiring public using (semiring)

-- Partially ordered idempotentSemiring (IdempotentPosemiring)

record IdempotentPosemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isIdempotentPosemiring : IsIdempotentPosemiring _≈_ _≤_ _+_ _*_ 0# 1#

  open IsIdempotentPosemiring isIdempotentPosemiring public

  idempotentProsemiring : IdempotentProsemiring c ℓ₁ ℓ₂
  idempotentProsemiring = record { isIdempotentProsemiring = isIdempotentProsemiring }

  open IdempotentProsemiring idempotentProsemiring public using (idempotentSemiring; +-idem)

-- Partially ordered KleeneAlgebra (PoKleeneAlgebra)

record PoKleeneAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infix  8 _⋆
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    _⋆            : Op₁ Carrier
    0#            : Carrier
    1#            : Carrier
    isPoKleeneAlgebra : IsPoKleeneAlgebra _≈_ _≤_ _+_ _*_ _⋆ 0# 1#

  open IsPoKleeneAlgebra isPoKleeneAlgebra public

  proKleeneAlgebra : ProKleeneAlgebra c ℓ₁ ℓ₂
  proKleeneAlgebra = record { isProKleeneAlgebra = isProKleeneAlgebra }

  open ProKleeneAlgebra proKleeneAlgebra public using (starExpansive; starDestructive)

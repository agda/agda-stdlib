------------------------------------------------------------------------
-- The Agda standard library
--
-- Residuated pomonoids and lattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Ordered.Residuated where

open import Algebra.Core using (Op₂)
open import Algebra.Bundles using (Monoid; Semiring)
open import Algebra.Ordered.Bundles
open import Data.Product using (proj₁; proj₂; swap)
open import Function using (flip)
open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.Lattice.Definitions using (Supremum)
open import Relation.Binary.Lattice.Bundles
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

------------------------------------------------------------------------
-- Structures

module _
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality
  (_≤_ : Rel A ℓ₂)       -- The partial order
  where

  -- FIXME: the definition of these structures should probably go into
  -- a separate module parametrized by _≈_ and _≤_, at which point
  -- these should go to the top.  But until it's clear where these
  -- should go, I'll keep this as is.

  open import Algebra.Definitions _≈_
  open import Algebra.Ordered.Structures _≈_ _≤_
  open import Algebra.Structures _≈_ using (IsMonoid; IsSemiring)
  open import Relation.Binary.Structures _≈_ using (IsPartialOrder)
  open import Relation.Binary.Lattice.Structures _≈_ _≤_

  -- Residuated pomonoids
  --
  -- TODO: should this remain here, in a separate module, or go into
  -- Algebra.Ordered.Structures?

  record IsRightResiduatedPomonoid
    (_∙_  : Op₂ A)     -- The monoid multiplication
    (_\\_ : Op₂ A)     -- The right residual
    (ε : A)            -- The monoid unit
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

    field
      isPartialOrder : IsPartialOrder _≤_
      ∙-mono₁        : ∀ z → Monotonic₁ _≤_ _≤_ (_∙ z)
      assoc          : Associative _∙_
      identity       : Identity ε _∙_
      adjoint        : ∀ {z} → Adjoint _≤_ _≤_ (z ∙_) (z \\_)

    open IsPartialOrder isPartialOrder public using (refl)

    unit : ∀ {x y} → y ≤ (x \\ (x ∙ y))
    unit = proj₁ adjoint refl

    counit : ∀ {x y} → (x ∙ (x \\ y)) ≤ y
    counit = proj₂ adjoint refl

    open PosetReasoning (record { isPartialOrder = isPartialOrder })

    ∙-mono₂ : ∀ z → Monotonic₁ _≤_ _≤_ (z ∙_)
    ∙-mono₂ z {x} {x′} x≤x′ = proj₂ adjoint (begin
      x               ≤⟨ x≤x′ ⟩
      x′              ≤⟨ unit ⟩
      z \\ (z ∙ x′)   ∎)

    ∙-mono : Monotonic₂ _≤_ _≤_ _≤_ _∙_
    ∙-mono {x} {x′} {y} {y′} x≤x′ y≤y′ = begin
      x  ∙ y    ≤⟨ ∙-mono₁ y  x≤x′ ⟩
      x′ ∙ y    ≤⟨ ∙-mono₂ x′ y≤y′ ⟩
      x′ ∙ y′   ∎

    isPomonoid : IsPomonoid _∙_ ε
    isPomonoid = record
      { isPosemigroup      = record
        { isPomagma        = record
          { isPartialOrder = isPartialOrder
          ; mono           = ∙-mono
          }
        ; assoc            = assoc
        }
      ; identity           = identity
      }

    open IsPomonoid isPomonoid public hiding
      ( isPartialOrder
      ; refl
      ; mono
      ; assoc
      ; identity
      )

    \\-anti₁ : ∀ z → Antitonic₁ _≤_ _≤_ (_\\ z)
    \\-anti₁ z {x} {x′} x≥x′ = proj₁ adjoint (begin
      x′ ∙ (x \\ z)   ≤⟨ ∙-mono₁ _ x≥x′ ⟩
      x  ∙ (x \\ z)   ≤⟨ counit         ⟩
      z               ∎)

    \\-mono₂ : ∀ z → Monotonic₁ _≤_ _≤_ (z \\_)
    \\-mono₂ z {x} {x′} x≤x′ = proj₁ adjoint (begin
      z ∙ (z \\ x)   ≤⟨ counit ⟩
      x              ≤⟨ x≤x′   ⟩
      x′             ∎)

    \\-mono :  AntitonicMonotonic _≤_ _≤_ _≤_ _\\_
    \\-mono {x} {x′} {y} {y′} x≥x′ y≤y′ = begin
      x  \\ y   ≤⟨ \\-anti₁ y  x≥x′ ⟩
      x′ \\ y   ≤⟨ \\-mono₂ x′ y≤y′ ⟩
      x′ \\ y′  ∎

  record IsResiduatedPomonoid (_∙_ : Op₂ A)     -- The monoid multiplication
                              (_//_ : Op₂ A)    -- The left residual
                              (_\\_ : Op₂ A)    -- The right residual
                              (ε : A)           -- The monoid unit
                              : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPartialOrder : IsPartialOrder _≤_
      assoc          : Associative _∙_
      identity       : Identity ε _∙_
      ∙-//-adjoint   : ∀ {z} → Adjoint _≤_ _≤_ (_∙ z) (_// z)
      ∙-\\-adjoint   : ∀ {z} → Adjoint _≤_ _≤_ (z ∙_) (z \\_)

    open IsPartialOrder isPartialOrder public using (refl)

    ∙-//-unit : ∀ {x y} → y ≤ ((y ∙ x) // x)
    ∙-//-unit = proj₁ ∙-//-adjoint refl

    open PosetReasoning (record { isPartialOrder = isPartialOrder })

    ∙-mono₁ : ∀ z → Monotonic₁ _≤_ _≤_ (_∙ z)
    ∙-mono₁ z {x} {x′} x≤x′ = proj₂ ∙-//-adjoint (begin
      x                ≤⟨ x≤x′      ⟩
      x′               ≤⟨ ∙-//-unit ⟩
      (x′ ∙ z) // z    ∎)

    isRightResiduatedPomonoid : IsRightResiduatedPomonoid _∙_ _\\_ ε
    isRightResiduatedPomonoid = record
      { isPartialOrder = isPartialOrder
      ; ∙-mono₁        = ∙-mono₁
      ; assoc          = assoc
      ; identity       = identity
      ; adjoint        = ∙-\\-adjoint
      }

    open IsRightResiduatedPomonoid isRightResiduatedPomonoid public
      renaming
        ( unit               to ∙-\\-unit
        ; counit             to ∙-\\-counit
        )
      hiding
        ( isPartialOrder
        ; refl
        ; ∙-mono₁
        ; assoc
        ; identity
        ; adjoint
        )

    isLeftResiduatedPomonoid : IsRightResiduatedPomonoid (flip _∙_) (flip _//_) ε
    isLeftResiduatedPomonoid = record
      { isPartialOrder      = isPartialOrder
      ; ∙-mono₁             = ∙-mono₂
      ; assoc               = λ x y z → Eq.sym (assoc z y x)
      ; identity            = swap identity
      ; adjoint             = ∙-//-adjoint
      }

    open IsRightResiduatedPomonoid isLeftResiduatedPomonoid public
      using () renaming
        ( counit   to ∙-//-counit
        ; \\-anti₁ to //-anti₂
        ; \\-mono₂ to //-mono₁
        ; \\-mono  to //-mono
        )

  ------------------------------------------------------------------------
  -- Residuated lattices

  -- Residuated semilattices
  --
  -- NOTE: We're only treating the join-case here, the meet-case is
  -- analogous.
  --
  -- TODO: should these definitions remain here, in a separate module in
  -- the Algebra.Ordered hiararchy, or go into
  -- Relation.Binary.Lattice.Structures?

  record IsRightResiduatedSemilattice
    (∨  : Op₂ A)     -- The join operation.
    (∙  : Op₂ A)     -- The monoid multiplication.
    (\\ : Op₂ A)     -- The right residual.
    (ε  : A)         -- The monoid unit.
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

    field
      isRightResiduatedPomonoid : IsRightResiduatedPomonoid ∙ \\ ε
      supremum                  : Supremum _≤_ ∨

    open IsRightResiduatedPomonoid isRightResiduatedPomonoid public

    isJoinSemilattice : IsJoinSemilattice ∨
    isJoinSemilattice = record
      { isPartialOrder = isPartialOrder
      ; supremum       = supremum
      }

  record IsResiduatedSemilattice
    (∨  : Op₂ A)     -- The join operation.
    (∙  : Op₂ A)     -- The monoid multiplication.
    (// : Op₂ A)     -- The left residual.
    (\\ : Op₂ A)     -- The right residual.
    (ε  : A)         -- The monoid unit.
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

    field
      isResiduatedPomonoid : IsResiduatedPomonoid ∙ // \\ ε
      supremum             : Supremum _≤_ ∨

    open IsResiduatedPomonoid isResiduatedPomonoid public

    isRightResiduatedSemilattice : IsRightResiduatedSemilattice ∨ ∙ \\ ε
    isRightResiduatedSemilattice = record
      { isRightResiduatedPomonoid = isRightResiduatedPomonoid
      ; supremum                  = supremum
      }

    isLeftResiduatedSemilattice
      : IsRightResiduatedSemilattice ∨ (flip ∙) (flip //) ε
    isLeftResiduatedSemilattice = record
      { isRightResiduatedPomonoid = isLeftResiduatedPomonoid
      ; supremum                  = supremum
      }

    open IsRightResiduatedSemilattice isRightResiduatedSemilattice public
      using (isJoinSemilattice)

  -- Residuated bounded semilattices

  record IsResiduatedBoundedSemilattice
    (∨ : Op₂ A)      -- The join operation.
    (∙ : Op₂ A)      -- The monoid multiplication.
    (// : Op₂ A)     -- The left residual.
    (\\ : Op₂ A)     -- The right residual.
    (⊥ : A)          -- The lattice minimum.
    (ε : A)          -- The monoid unit.
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

    field
      isResiduatedPomonoid : IsResiduatedPomonoid ∙ // \\ ε
      supremum             : Supremum _≤_ ∨
      minimum              : Minimum _≤_ ⊥

    open IsResiduatedPomonoid isResiduatedPomonoid public

    isResiduatedSemilattice : IsResiduatedSemilattice ∨ ∙ // \\ ε
    isResiduatedSemilattice = record
      { isResiduatedPomonoid = isResiduatedPomonoid
      ; supremum             = supremum
      }
    open IsResiduatedSemilattice isResiduatedSemilattice public using
      ( isJoinSemilattice
      ; isRightResiduatedSemilattice
      ; isLeftResiduatedSemilattice
      )

    isBoundedJoinSemilattice : IsBoundedJoinSemilattice ∨ ⊥
    isBoundedJoinSemilattice = record
      { isJoinSemilattice = isJoinSemilattice
      ; minimum           = minimum
      }

------------------------------------------------------------------------
-- Bundles
--
-- FIXME: should these go into a separate module?  If so, where?

-- Residuated pomonoids

record RightResiduatedPomonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  infixl 6 _\\_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    _\\_    : Op₂ Carrier     -- The right residual.
    ε       : Carrier         -- The monoid unit.
    isRightResiduatedPomonoid : IsRightResiduatedPomonoid _≈_ _≤_ _∙_ _\\_ ε

  open IsRightResiduatedPomonoid isRightResiduatedPomonoid public

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

record ResiduatedPomonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  infixl 6 _//_ _\\_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    _//_    : Op₂ Carrier     -- The left residual.
    _\\_    : Op₂ Carrier     -- The right residual.
    ε       : Carrier         -- The monoid unit.
    isResiduatedPomonoid : IsResiduatedPomonoid _≈_ _≤_ _∙_ _//_ _\\_ ε

  open IsResiduatedPomonoid isResiduatedPomonoid public

  leftResiduatedPomonoid : RightResiduatedPomonoid c ℓ₁ ℓ₂
  leftResiduatedPomonoid = record
    { isRightResiduatedPomonoid = isLeftResiduatedPomonoid }

  rightResiduatedPomonoid : RightResiduatedPomonoid c ℓ₁ ℓ₂
  rightResiduatedPomonoid = record
    { isRightResiduatedPomonoid = isRightResiduatedPomonoid }

  open RightResiduatedPomonoid rightResiduatedPomonoid public
    using (preorder; poset; pomonoid; semigroup; monoid)

-- Residuated semilattices

record RightResiduatedSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∨_     : Op₂ Carrier     -- The join operation.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    _\\_    : Op₂ Carrier     -- The right residual.
    ε       : Carrier         -- The monoid unit.
    isRightResiduatedSemilattice
      : IsRightResiduatedSemilattice _≈_ _≤_ _∨_ _∙_ _\\_ ε

  open IsRightResiduatedSemilattice isRightResiduatedSemilattice public

  rightResiduatedPomonoid : RightResiduatedPomonoid c ℓ₁ ℓ₂
  rightResiduatedPomonoid = record
    { isRightResiduatedPomonoid = isRightResiduatedPomonoid }

  open RightResiduatedPomonoid public
    using (preorder; poset; pomonoid; semigroup; monoid)

  joinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
  joinSemilattice = record { isJoinSemilattice = isJoinSemilattice }

record ResiduatedSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∨_     : Op₂ Carrier     -- The join operation.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    _//_    : Op₂ Carrier     -- The left residual.
    _\\_    : Op₂ Carrier     -- The right residual.
    ε       : Carrier         -- The monoid unit.
    isResiduatedSemilattice
      : IsResiduatedSemilattice _≈_ _≤_ _∨_ _∙_ _//_ _\\_ ε

  open IsResiduatedSemilattice isResiduatedSemilattice public

  residuatedPomonoid : ResiduatedPomonoid c ℓ₁ ℓ₂
  residuatedPomonoid = record { isResiduatedPomonoid = isResiduatedPomonoid }

  open ResiduatedPomonoid residuatedPomonoid public using
    ( leftResiduatedPomonoid
    ; rightResiduatedPomonoid
    ; preorder
    ; poset
    ; pomonoid
    ; semigroup
    ; monoid
    )

  leftResiduatedSemilattice : RightResiduatedSemilattice c ℓ₁ ℓ₂
  leftResiduatedSemilattice = record
    { isRightResiduatedSemilattice = isLeftResiduatedSemilattice }

  rightResiduatedSemilattice : RightResiduatedSemilattice c ℓ₁ ℓ₂
  rightResiduatedSemilattice = record
    { isRightResiduatedSemilattice = isRightResiduatedSemilattice }

  open RightResiduatedSemilattice rightResiduatedSemilattice public
    using (joinSemilattice)

-- Residuated bounded semilattices

record ResiduatedBoundedSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∨_     : Op₂ Carrier     -- The join operation.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    _//_    : Op₂ Carrier     -- The left residual.
    _\\_    : Op₂ Carrier     -- The right residual.
    ⊥       : Carrier         -- The lattice minimum.
    ε       : Carrier         -- The monoid unit.
    isResiduatedBoundedSemilattice
      : IsResiduatedBoundedSemilattice _≈_ _≤_ _∨_ _∙_ _//_ _\\_ ⊥ ε

  open IsResiduatedBoundedSemilattice isResiduatedBoundedSemilattice public

  residuatedSemilattice : ResiduatedSemilattice c ℓ₁ ℓ₂
  residuatedSemilattice = record
    { isResiduatedSemilattice = isResiduatedSemilattice }

  open ResiduatedSemilattice residuatedSemilattice public using
    ( preorder
    ; poset
    ; pomonoid
    ; rightResiduatedPomonoid
    ; leftResiduatedPomonoid
    ; joinSemilattice
    ; leftResiduatedSemilattice
    ; rightResiduatedSemilattice
    ; semigroup
    ; monoid
    )

  boundedJoinSemilattice : BoundedJoinSemilattice c ℓ₁ ℓ₂
  boundedJoinSemilattice = record
    { isBoundedJoinSemilattice = isBoundedJoinSemilattice }

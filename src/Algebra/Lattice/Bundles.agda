------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like semilattices and lattices
-- (packed in records together with sets, operations, etc.), defined via
-- meet/join operations and their properties
--
-- For lattices defined via an order relation, see
-- Relation.Binary.Lattice.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Lattice`.

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Lattice.Bundles where

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures
import Algebra.Lattice.Bundles.Raw as Raw
open import Algebra.Lattice.Structures
open import Level using (suc; _⊔_)
open import Relation.Binary

------------------------------------------------------------------------
-- Re-export definitions of 'raw' bundles

open Raw public
  using (RawLattice)

------------------------------------------------------------------------
-- Bundles
------------------------------------------------------------------------

record Semilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∙_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _∙_           : Op₂ Carrier
    isSemilattice : IsSemilattice _≈_ _∙_

  open IsSemilattice isSemilattice public

  band : Band c ℓ
  band = record { isBand = isBand }

  open Band band public
    using (_≉_; rawMagma; magma; isMagma; semigroup; isSemigroup; isBand)


record MeetSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _∧_               : Op₂ Carrier
    isMeetSemilattice : IsSemilattice _≈_ _∧_

  open IsMeetSemilattice _≈_ isMeetSemilattice public

  semilattice : Semilattice c ℓ
  semilattice = record { isSemilattice = isMeetSemilattice }

  open Semilattice semilattice public
    using (rawMagma; magma; semigroup; band)


record JoinSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∨_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _∨_               : Op₂ Carrier
    isJoinSemilattice : IsSemilattice _≈_ _∨_

  open IsJoinSemilattice _≈_ isJoinSemilattice public

  semilattice : Semilattice c ℓ
  semilattice = record { isSemilattice = isJoinSemilattice }

  open Semilattice semilattice public
    using (rawMagma; magma; semigroup; band)


record BoundedSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∙_
  infix  4 _≈_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ
    _∙_                  : Op₂ Carrier
    ε                    : Carrier
    isBoundedSemilattice : IsBoundedSemilattice _≈_ _∙_ ε

  open IsBoundedSemilattice _≈_ isBoundedSemilattice public

  semilattice : Semilattice c ℓ
  semilattice = record { isSemilattice = isSemilattice }

  open Semilattice semilattice public using (rawMagma; magma; semigroup; band)


record BoundedMeetSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infix  4 _≈_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ
    _∧_                      : Op₂ Carrier
    ⊤                        : Carrier
    isBoundedMeetSemilattice : IsBoundedSemilattice _≈_ _∧_ ⊤

  open IsBoundedMeetSemilattice _≈_ isBoundedMeetSemilattice public

  boundedSemilattice : BoundedSemilattice c ℓ
  boundedSemilattice = record
    { isBoundedSemilattice = isBoundedMeetSemilattice }

  open BoundedSemilattice boundedSemilattice public
    using (rawMagma; magma; semigroup; band; semilattice)


record BoundedJoinSemilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∨_
  infix  4 _≈_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ
    _∨_                      : Op₂ Carrier
    ⊥                        : Carrier
    isBoundedJoinSemilattice : IsBoundedSemilattice _≈_ _∨_ ⊥

  open IsBoundedJoinSemilattice _≈_ isBoundedJoinSemilattice public

  boundedSemilattice : BoundedSemilattice c ℓ
  boundedSemilattice = record
    { isBoundedSemilattice = isBoundedJoinSemilattice }

  open BoundedSemilattice boundedSemilattice public
    using (rawMagma; magma; semigroup; band; semilattice)


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

  rawLattice : RawLattice c ℓ
  rawLattice = record
    { _≈_  = _≈_
    ; _∧_  = _∧_
    ; _∨_  = _∨_
    }

  open RawLattice rawLattice public
    using (∨-rawMagma; ∧-rawMagma)

  setoid : Setoid c ℓ
  setoid = record { isEquivalence = isEquivalence }

  open Setoid setoid public
    using (_≉_)


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

  open Lattice lattice public
    using
    ( _≉_; setoid; rawLattice
    ; ∨-rawMagma; ∧-rawMagma
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
  distributiveLattice = record
    { isDistributiveLattice = isDistributiveLattice
    }

  open DistributiveLattice distributiveLattice public
    using
    ( _≉_; setoid; rawLattice
    ; ∨-rawMagma; ∧-rawMagma
    ; lattice
    )

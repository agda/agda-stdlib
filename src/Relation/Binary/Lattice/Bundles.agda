------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for order-theoretic lattices
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Lattice`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Lattice.Bundles where

open import Algebra.Core using (Op₁; Op₂)
open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Poset; Setoid)
open import Relation.Binary.Lattice.Structures

------------------------------------------------------------------------
-- Join semilattices

record JoinSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_               : Rel Carrier ℓ₂  -- The partial order.
    _∨_               : Op₂ Carrier     -- The join operation.
    isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_

  open IsJoinSemilattice isJoinSemilattice public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)


record BoundedJoinSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                      : Rel Carrier ℓ₂  -- The partial order.
    _∨_                      : Op₂ Carrier     -- The join operation.
    ⊥                        : Carrier         -- The minimum.
    isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥

  open IsBoundedJoinSemilattice isBoundedJoinSemilattice public

  joinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
  joinSemilattice = record { isJoinSemilattice = isJoinSemilattice }

  open JoinSemilattice joinSemilattice public using (preorder; poset)

------------------------------------------------------------------------
-- Meet semilattices

record MeetSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 7 _∧_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_               : Rel Carrier ℓ₂  -- The partial order.
    _∧_               : Op₂ Carrier     -- The meet operation.
    isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_

  open IsMeetSemilattice isMeetSemilattice public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

record BoundedMeetSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 7 _∧_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                      : Rel Carrier ℓ₂  -- The partial order.
    _∧_                      : Op₂ Carrier     -- The join operation.
    ⊤                        : Carrier         -- The maximum.
    isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤

  open IsBoundedMeetSemilattice isBoundedMeetSemilattice public

  meetSemilattice : MeetSemilattice c ℓ₁ ℓ₂
  meetSemilattice = record { isMeetSemilattice = isMeetSemilattice }

  open MeetSemilattice meetSemilattice public using (preorder; poset)

------------------------------------------------------------------------
-- Lattices

record Lattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_       : Rel Carrier ℓ₂  -- The partial order.
    _∨_       : Op₂ Carrier     -- The join operation.
    _∧_       : Op₂ Carrier     -- The meet operation.
    isLattice : IsLattice _≈_ _≤_ _∨_ _∧_

  open IsLattice isLattice public

  setoid : Setoid c ℓ₁
  setoid = record { isEquivalence = isEquivalence }

  joinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
  joinSemilattice = record { isJoinSemilattice = isJoinSemilattice }

  meetSemilattice : MeetSemilattice c ℓ₁ ℓ₂
  meetSemilattice = record { isMeetSemilattice = isMeetSemilattice }

  open JoinSemilattice joinSemilattice public using (poset; preorder)

record DistributiveLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∨_     : Op₂ Carrier     -- The join operation.
    _∧_     : Op₂ Carrier     -- The meet operation.
    isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice using (∧-distribˡ-∨) public
  open IsDistributiveLattice isDistributiveLattice using (isLattice)

  lattice : Lattice c ℓ₁ ℓ₂
  lattice = record { isLattice = isLattice }

  open Lattice lattice hiding (Carrier; _≈_; _≤_; _∨_; _∧_) public

record BoundedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_              : Rel Carrier ℓ₂  -- The partial order.
    _∨_              : Op₂ Carrier     -- The join operation.
    _∧_              : Op₂ Carrier     -- The meet operation.
    ⊤                : Carrier         -- The maximum.
    ⊥                : Carrier         -- The minimum.
    isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥

  open IsBoundedLattice isBoundedLattice public

  boundedJoinSemilattice : BoundedJoinSemilattice c ℓ₁ ℓ₂
  boundedJoinSemilattice = record
    { isBoundedJoinSemilattice = isBoundedJoinSemilattice }

  boundedMeetSemilattice : BoundedMeetSemilattice c ℓ₁ ℓ₂
  boundedMeetSemilattice = record
    { isBoundedMeetSemilattice = isBoundedMeetSemilattice }

  lattice : Lattice c ℓ₁ ℓ₂
  lattice = record { isLattice = isLattice }

  open Lattice lattice public
    using (joinSemilattice; meetSemilattice; poset; preorder; setoid)

------------------------------------------------------------------------
-- Heyting algebras (a bounded lattice with exponential operator)

record HeytingAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 5 _⇨_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_              : Rel Carrier ℓ₂  -- The partial order.
    _∨_              : Op₂ Carrier     -- The join operation.
    _∧_              : Op₂ Carrier     -- The meet operation.
    _⇨_              : Op₂ Carrier     -- The exponential operation.
    ⊤                : Carrier         -- The maximum.
    ⊥                : Carrier         -- The minimum.
    isHeytingAlgebra : IsHeytingAlgebra _≈_ _≤_ _∨_ _∧_ _⇨_ ⊤ ⊥

  boundedLattice : BoundedLattice c ℓ₁ ℓ₂
  boundedLattice = record
    { isBoundedLattice = IsHeytingAlgebra.isBoundedLattice isHeytingAlgebra }

  open IsHeytingAlgebra isHeytingAlgebra
    using (exponential; transpose-⇨; transpose-∧) public
  open BoundedLattice boundedLattice
    hiding (Carrier; _≈_; _≤_; _∨_; _∧_; ⊤; ⊥) public

------------------------------------------------------------------------
-- Boolean algebras (a specialized Heyting algebra)

record BooleanAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  infix 8 ¬_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_              : Rel Carrier ℓ₂  -- The partial order.
    _∨_              : Op₂ Carrier     -- The join operation.
    _∧_              : Op₂ Carrier     -- The meet operation.
    ¬_               : Op₁ Carrier     -- The negation operation.
    ⊤                : Carrier         -- The maximum.
    ⊥                : Carrier         -- The minimum.
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _≤_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra using (isHeytingAlgebra)

  heytingAlgebra : HeytingAlgebra c ℓ₁ ℓ₂
  heytingAlgebra = record { isHeytingAlgebra = isHeytingAlgebra }

  open HeytingAlgebra heytingAlgebra public
    hiding (Carrier; _≈_; _≤_; _∨_; _∧_; ⊤; ⊥)

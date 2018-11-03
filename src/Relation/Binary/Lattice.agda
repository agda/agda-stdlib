------------------------------------------------------------------------
-- The Agda standard library
--
-- Order-theoretic lattices
------------------------------------------------------------------------

module Relation.Binary.Lattice where

open import Algebra.FunctionProperties
open import Data.Product using (_×_; _,_)
open import Function using (flip)
open import Level using (suc; _⊔_)
open import Relation.Binary

------------------------------------------------------------------------
-- Relationships between orders and operators

open import Relation.Binary public using (Maximum; Minimum)

Supremum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Supremum _≤_ _∨_ =
  ∀ x y → x ≤ (x ∨ y) × y ≤ (x ∨ y) × ∀ z → x ≤ z → y ≤ z → (x ∨ y) ≤ z

Infimum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Infimum _≤_ = Supremum (flip _≤_)

Exponential : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Op₂ A → Set _
Exponential _≤_ _∧_ _⇨_ =
  ∀ w x y → ((w ∧ x) ≤ y → w ≤ (x ⇨ y)) × (w ≤ (x ⇨ y) → (w ∧ x) ≤ y)

------------------------------------------------------------------------
-- Join semilattices

record IsJoinSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) -- The underlying equality.
                         (_≤_ : Rel A ℓ₂) -- The partial order.
                         (_∨_ : Op₂ A)    -- The join operation.
                         : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    supremum       : Supremum _≤_ _∨_

  x≤x∨y : ∀ x y → x ≤ (x ∨ y)
  x≤x∨y x y = let pf , _ , _ = supremum x y in pf

  y≤x∨y : ∀ x y → y ≤ (x ∨ y)
  y≤x∨y x y = let _ , pf , _ = supremum x y in pf

  ∨-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  ∨-least {x} {y} {z} = let _ , _ , pf = supremum x y in pf z

  open IsPartialOrder isPartialOrder public

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

record IsBoundedJoinSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                                (_≈_ : Rel A ℓ₁) -- The underlying equality.
                                (_≤_ : Rel A ℓ₂) -- The partial order.
                                (_∨_ : Op₂ A)    -- The join operation.
                                (⊥   : A)        -- The minimum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
    minimum           : Minimum _≤_ ⊥

  open IsJoinSemilattice isJoinSemilattice public

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

  joinSemiLattice = joinSemilattice
  {-# WARNING_ON_USAGE joinSemiLattice
  "Warning: joinSemiLattice was deprecated in v0.17.
  Please use joinSemilattice instead."
  #-}

  open JoinSemilattice joinSemilattice public using (preorder; poset)

------------------------------------------------------------------------
-- Meet semilattices

record IsMeetSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) -- The underlying equality.
                         (_≤_ : Rel A ℓ₂) -- The partial order.
                         (_∧_ : Op₂ A)    -- The meet operation.
                         : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    infimum        : Infimum _≤_ _∧_

  x∧y≤x : ∀ x y → (x ∧ y) ≤ x
  x∧y≤x x y = let pf , _ , _ = infimum x y in pf

  x∧y≤y : ∀ x y → (x ∧ y) ≤ y
  x∧y≤y x y = let _ , pf , _ = infimum x y in pf

  ∧-greatest : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ∧ z)
  ∧-greatest {x} {y} {z} = let _ , _ , pf = infimum y z in pf x

  open IsPartialOrder isPartialOrder public

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

record IsBoundedMeetSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                                (_≈_ : Rel A ℓ₁) -- The underlying equality.
                                (_≤_ : Rel A ℓ₂) -- The partial order.
                                (_∧_ : Op₂ A)    -- The join operation.
                                (⊤   : A)        -- The maximum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
    maximum           : Maximum _≤_ ⊤

  open IsMeetSemilattice isMeetSemilattice public

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

  meetSemiLattice = meetSemilattice
  {-# WARNING_ON_USAGE meetSemiLattice
  "Warning: meetSemiLattice was deprecated in v0.17.
  Please use meetSemilattice instead."
  #-}

  open MeetSemilattice meetSemilattice public using (preorder; poset)

------------------------------------------------------------------------
-- Lattices

record IsLattice {a ℓ₁ ℓ₂} {A : Set a}
                 (_≈_ : Rel A ℓ₁) -- The underlying equality.
                 (_≤_ : Rel A ℓ₂) -- The partial order.
                 (_∨_ : Op₂ A)    -- The join operation.
                 (_∧_ : Op₂ A)    -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    supremum       : Supremum _≤_ _∨_
    infimum        : Infimum _≤_ _∧_

  isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
  isJoinSemilattice = record
    { isPartialOrder = isPartialOrder
    ; supremum       = supremum
    }

  isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
  isMeetSemilattice = record
    { isPartialOrder = isPartialOrder
    ; infimum        = infimum
    }

  open IsJoinSemilattice isJoinSemilattice public
    using (x≤x∨y; y≤x∨y; ∨-least)
  open IsMeetSemilattice isMeetSemilattice public
    using (x∧y≤x; x∧y≤y; ∧-greatest)
  open IsPartialOrder isPartialOrder public

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

record IsDistributiveLattice {a ℓ₁ ℓ₂} {A : Set a}
                             (_≈_ : Rel A ℓ₁) -- The underlying equality.
                             (_≤_ : Rel A ℓ₂) -- The partial order.
                             (_∨_ : Op₂ A)    -- The join operation.
                             (_∧_ : Op₂ A)    -- The meet operation.
                             : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLattice    : IsLattice _≈_ _≤_ _∨_ _∧_
    ∧-distribˡ-∨ : _DistributesOverˡ_ _≈_ _∧_ _∨_

  open IsLattice isLattice public

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

record IsBoundedLattice {a ℓ₁ ℓ₂} {A : Set a}
                        (_≈_ : Rel A ℓ₁) -- The underlying equality.
                        (_≤_ : Rel A ℓ₂) -- The partial order.
                        (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
    maximum   : Maximum _≤_ ⊤
    minimum   : Minimum _≤_ ⊥

  open IsLattice isLattice public

  isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥
  isBoundedJoinSemilattice = record
    { isJoinSemilattice = isJoinSemilattice
    ; minimum           = minimum
    }

  isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤
  isBoundedMeetSemilattice = record
    { isMeetSemilattice = isMeetSemilattice
    ; maximum           = maximum
    }

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

record IsHeytingAlgebra {a ℓ₁ ℓ₂} {A : Set a}
                        (_≈_ : Rel A ℓ₁) -- The underlying equality.
                        (_≤_ : Rel A ℓ₂) -- The partial order.
                        (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (_⇨_ : Op₂ A)    -- The exponential operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥
    exponential      : Exponential _≤_ _∧_ _⇨_

  transpose-⇨ : ∀ {w x y} → (w ∧ x) ≤ y → w ≤ (x ⇨ y)
  transpose-⇨ {w} {x} {y} = let pf , _ = exponential w x y in pf

  transpose-∧ : ∀ {w x y} → w ≤ (x ⇨ y) → (w ∧ x) ≤ y
  transpose-∧ {w} {x} {y} = let _ , pf = exponential w x y in pf

  open IsBoundedLattice isBoundedLattice public

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

record IsBooleanAlgebra {a ℓ₁ ℓ₂} {A : Set a}
                        (_≈_ : Rel A ℓ₁) -- The underlying equality.
                        (_≤_ : Rel A ℓ₂) -- The partial order.
                        (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (¬_ : Op₁ A)     -- The negation operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infixr 5 _⇨_
  _⇨_ : Op₂ A
  x ⇨ y = (¬ x) ∨ y

  field
    isHeytingAlgebra : IsHeytingAlgebra _≈_ _≤_ _∨_ _∧_ _⇨_ ⊤ ⊥

  open IsHeytingAlgebra isHeytingAlgebra public

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

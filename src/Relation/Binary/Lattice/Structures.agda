------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for order-theoretic lattices
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Lattice`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary

module Relation.Binary.Lattice.Structures
 {a ℓ₁ ℓ₂} {A : Set a}
 (_≈_ : Rel A ℓ₁) -- The underlying equality.
 (_≤_ : Rel A ℓ₂) -- The partial order.
 where

open import Algebra.Core
open import Algebra.Definitions
open import Data.Product.Base using (_×_; _,_)
open import Level using (suc; _⊔_)

open import Relation.Binary.Lattice.Definitions

------------------------------------------------------------------------
-- Join semilattices

record IsJoinSemilattice (_∨_ : Op₂ A)    -- The join operation.
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

record IsBoundedJoinSemilattice (_∨_ : Op₂ A)    -- The join operation.
                                (⊥   : A)        -- The minimum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isJoinSemilattice : IsJoinSemilattice _∨_
    minimum           : Minimum _≤_ ⊥

  open IsJoinSemilattice isJoinSemilattice public

------------------------------------------------------------------------
-- Meet semilattices

record IsMeetSemilattice (_∧_ : Op₂ A)    -- The meet operation.
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

record IsBoundedMeetSemilattice (_∧_ : Op₂ A)    -- The join operation.
                                (⊤   : A)        -- The maximum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMeetSemilattice : IsMeetSemilattice _∧_
    maximum           : Maximum _≤_ ⊤

  open IsMeetSemilattice isMeetSemilattice public

------------------------------------------------------------------------
-- Lattices

record IsLattice (_∨_ : Op₂ A)    -- The join operation.
                 (_∧_ : Op₂ A)    -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    supremum       : Supremum _≤_ _∨_
    infimum        : Infimum _≤_ _∧_

  isJoinSemilattice : IsJoinSemilattice  _∨_
  isJoinSemilattice = record
    { isPartialOrder = isPartialOrder
    ; supremum       = supremum
    }

  isMeetSemilattice : IsMeetSemilattice  _∧_
  isMeetSemilattice = record
    { isPartialOrder = isPartialOrder
    ; infimum        = infimum
    }

  open IsJoinSemilattice isJoinSemilattice public
    using (x≤x∨y; y≤x∨y; ∨-least)
  open IsMeetSemilattice isMeetSemilattice public
    using (x∧y≤x; x∧y≤y; ∧-greatest)
  open IsPartialOrder isPartialOrder public

record IsDistributiveLattice (_∨_ : Op₂ A)    -- The join operation.
                             (_∧_ : Op₂ A)    -- The meet operation.
                             : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLattice    : IsLattice _∨_ _∧_
    ∧-distribˡ-∨ : _DistributesOverˡ_ _≈_ _∧_ _∨_

  open IsLattice isLattice public

record IsBoundedLattice (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLattice : IsLattice _∨_ _∧_
    maximum   : Maximum _≤_ ⊤
    minimum   : Minimum _≤_ ⊥

  open IsLattice isLattice public

  isBoundedJoinSemilattice : IsBoundedJoinSemilattice  _∨_ ⊥
  isBoundedJoinSemilattice = record
    { isJoinSemilattice = isJoinSemilattice
    ; minimum           = minimum
    }

  isBoundedMeetSemilattice : IsBoundedMeetSemilattice _∧_ ⊤
  isBoundedMeetSemilattice = record
    { isMeetSemilattice = isMeetSemilattice
    ; maximum           = maximum
    }

------------------------------------------------------------------------
-- Heyting algebras (a bounded lattice with exponential operator)

record IsHeytingAlgebra (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (_⇨_ : Op₂ A)    -- The exponential operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isBoundedLattice : IsBoundedLattice _∨_ _∧_ ⊤ ⊥
    exponential      : Exponential _≤_ _∧_ _⇨_

  transpose-⇨ : ∀ {w x y} → (w ∧ x) ≤ y → w ≤ (x ⇨ y)
  transpose-⇨ {w} {x} {y} = let pf , _ = exponential w x y in pf

  transpose-∧ : ∀ {w x y} → w ≤ (x ⇨ y) → (w ∧ x) ≤ y
  transpose-∧ {w} {x} {y} = let _ , pf = exponential w x y in pf

  open IsBoundedLattice isBoundedLattice public

------------------------------------------------------------------------
-- Boolean algebras (a specialized Heyting algebra)

record IsBooleanAlgebra (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (¬_ : Op₁ A)     -- The negation operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infixr 5 _⇨_
  _⇨_ : Op₂ A
  x ⇨ y = (¬ x) ∨ y

  field
    isHeytingAlgebra : IsHeytingAlgebra _∨_ _∧_ _⇨_ ⊤ ⊥

  open IsHeytingAlgebra isHeytingAlgebra public

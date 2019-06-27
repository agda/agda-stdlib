------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open Lattice L
open import Algebra.Structures _≈_
open import Algebra.FunctionProperties _≈_
import Algebra.Properties.Semilattice as SemilatticeProperties
open import Relation.Binary
import Relation.Binary.Lattice as R
open import Relation.Binary.Reasoning.Setoid  setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product using (_,_; swap)

------------------------------------------------------------------------
-- _∧_ is a semilattice

∧-idem : Idempotent _∧_
∧-idem x = begin
  x ∧ x            ≈⟨ ∧-congˡ (sym (∨-absorbs-∧ _ _)) ⟩
  x ∧ (x ∨ x ∧ x)  ≈⟨ ∧-absorbs-∨ _ _ ⟩
  x                ∎

∧-isMagma : IsMagma _∧_
∧-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ∧-cong
  }

∧-isSemigroup : IsSemigroup _∧_
∧-isSemigroup = record
  { isMagma = ∧-isMagma
  ; assoc   = ∧-assoc
  }

∧-isBand : IsBand _∧_
∧-isBand = record
  { isSemigroup = ∧-isSemigroup
  ; idem        = ∧-idem
  }

∧-isSemilattice : IsSemilattice _∧_
∧-isSemilattice = record
  { isBand = ∧-isBand
  ; comm   = ∧-comm
  }

∧-semilattice : Semilattice l₁ l₂
∧-semilattice = record
  { isSemilattice = ∧-isSemilattice
  }

open SemilatticeProperties ∧-semilattice public
  using
  ( ∧-isOrderTheoreticMeetSemilattice
  ; ∧-isOrderTheoreticJoinSemilattice
  ; ∧-orderTheoreticMeetSemilattice
  ; ∧-orderTheoreticJoinSemilattice
  )

------------------------------------------------------------------------
-- _∨_ is a semilattice

∨-idem : Idempotent _∨_
∨-idem x = begin
  x ∨ x      ≈⟨ ∨-congˡ (sym (∧-idem _)) ⟩
  x ∨ x ∧ x  ≈⟨ ∨-absorbs-∧ _ _ ⟩
  x          ∎

∨-isMagma : IsMagma _∨_
∨-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ∨-cong
  }

∨-isSemigroup : IsSemigroup _∨_
∨-isSemigroup = record
  { isMagma = ∨-isMagma
  ; assoc   = ∨-assoc
  }

∨-isBand : IsBand _∨_
∨-isBand = record
  { isSemigroup = ∨-isSemigroup
  ; idem        = ∨-idem
  }

∨-isSemilattice : IsSemilattice _∨_
∨-isSemilattice = record
  { isBand = ∨-isBand
  ; comm   = ∨-comm
  }

∨-semilattice : Semilattice l₁ l₂
∨-semilattice = record
  { isSemilattice = ∨-isSemilattice
  }

open SemilatticeProperties ∨-semilattice public
  using ()
  renaming
  ( ∧-isOrderTheoreticMeetSemilattice to ∨-isOrderTheoreticMeetSemilattice
  ; ∧-isOrderTheoreticJoinSemilattice to ∨-isOrderTheoreticJoinSemilattice
  ; ∧-orderTheoreticMeetSemilattice   to ∨-orderTheoreticMeetSemilattice
  ; ∧-orderTheoreticJoinSemilattice   to ∨-orderTheoreticJoinSemilattice
  )

------------------------------------------------------------------------
-- The dual construction is also a lattice.

∧-∨-isLattice : IsLattice _∧_ _∨_
∧-∨-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ∧-comm
  ; ∨-assoc       = ∧-assoc
  ; ∨-cong        = ∧-cong
  ; ∧-comm        = ∨-comm
  ; ∧-assoc       = ∨-assoc
  ; ∧-cong        = ∨-cong
  ; absorptive    = swap absorptive
  }

∧-∨-lattice : Lattice _ _
∧-∨-lattice = record
  { isLattice = ∧-∨-isLattice
  }

------------------------------------------------------------------------
-- Every algebraic lattice can be turned into an order-theoretic one.

open SemilatticeProperties ∧-semilattice public using (poset)
open Poset poset using (_≤_; isPartialOrder)

∨-∧-isOrderTheoreticLattice : R.IsLattice _≈_ _≤_ _∨_ _∧_
∨-∧-isOrderTheoreticLattice = record
  { isPartialOrder = isPartialOrder
  ; supremum       = supremum
  ; infimum        = infimum
  }
  where
  open R.MeetSemilattice ∧-orderTheoreticMeetSemilattice using (infimum)
  open R.JoinSemilattice ∨-orderTheoreticJoinSemilattice using (x≤x∨y; y≤x∨y; ∨-least)
    renaming (_≤_ to _≤′_)

  -- An alternative but equivalent interpretation of the order _≤_.

  sound : ∀ {x y} → x ≤′ y → x ≤ y
  sound {x} {y} y≈y∨x = sym $ begin
    x ∧ y        ≈⟨ ∧-congˡ y≈y∨x ⟩
    x ∧ (y ∨ x)  ≈⟨ ∧-congˡ (∨-comm y x) ⟩
    x ∧ (x ∨ y)  ≈⟨ ∧-absorbs-∨ x y ⟩
    x            ∎

  complete : ∀ {x y} → x ≤ y → x ≤′ y
  complete {x} {y} x≈x∧y = sym $ begin
    y ∨ x        ≈⟨ ∨-congˡ x≈x∧y ⟩
    y ∨ (x ∧ y)  ≈⟨ ∨-congˡ (∧-comm x y) ⟩
    y ∨ (y ∧ x)  ≈⟨ ∨-absorbs-∧ y x ⟩
    y            ∎

  supremum : R.Supremum _≤_ _∨_
  supremum x y =
     sound (x≤x∨y x y) ,
     sound (y≤x∨y x y) ,
     λ z x≤z y≤z → sound (∨-least (complete x≤z) (complete y≤z))

∨-∧-orderTheoreticLattice : R.Lattice _ _ _
∨-∧-orderTheoreticLattice = record
  { isLattice = ∨-∧-isOrderTheoreticLattice
  }

------------------------------------------------------------------------
-- One can replace the underlying equality with an equivalent one.

replace-equality : {_≈′_ : Rel Carrier l₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) → Lattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_       = _≈′_
  ; _∧_       = _∧_
  ; _∨_       = _∨_
  ; isLattice = record
    { isEquivalence = record
      { refl  = to ⟨$⟩ refl
      ; sym   = λ x≈y → to ⟨$⟩ sym (from ⟨$⟩ x≈y)
      ; trans = λ x≈y y≈z → to ⟨$⟩ trans (from ⟨$⟩ x≈y) (from ⟨$⟩ y≈z)
      }
    ; ∨-comm     = λ x y → to ⟨$⟩ ∨-comm x y
    ; ∨-assoc    = λ x y z → to ⟨$⟩ ∨-assoc x y z
    ; ∨-cong     = λ x≈y u≈v → to ⟨$⟩ ∨-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; ∧-comm     = λ x y → to ⟨$⟩ ∧-comm x y
    ; ∧-assoc    = λ x y z → to ⟨$⟩ ∧-assoc x y z
    ; ∧-cong     = λ x≈y u≈v → to ⟨$⟩ ∧-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; absorptive = (λ x y → to ⟨$⟩ ∨-absorbs-∧ x y)
                 , (λ x y → to ⟨$⟩ ∧-absorbs-∨ x y)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

∧-idempotent = ∧-idem
{-# WARNING_ON_USAGE ∧-idempotent
"Warning: ∧-idempotent was deprecated in v1.1.
Please use ∧-idem instead."
#-}
∨-idempotent = ∨-idem
{-# WARNING_ON_USAGE ∨-idempotent
"Warning: ∨-idempotent was deprecated in v1.1.
Please use ∨-idem instead."
#-}
isOrderTheoreticLattice = ∨-∧-isOrderTheoreticLattice
{-# WARNING_ON_USAGE isOrderTheoreticLattice
"Warning: isOrderTheoreticLattice was deprecated in v1.1.
Please use ∨-∧-isOrderTheoreticLattice instead."
#-}
orderTheoreticLattice = ∨-∧-orderTheoreticLattice
{-# WARNING_ON_USAGE orderTheoreticLattice
"Warning: orderTheoreticLattice was deprecated in v1.1.
Please use ∨-∧-orderTheoreticLattice instead."
#-}

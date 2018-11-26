------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.Semilattice {l₁ l₂} (L : Semilattice l₁ l₂) where

open Semilattice L
open import Algebra.Structures
open import Relation.Binary
import Relation.Binary.Lattice as R
import Relation.Binary.Properties.Poset as R
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

-- Every semilattice can be turned into a poset.

poset : Poset _ _ _
poset = record
  { Carrier        = Carrier
  ; _≈_            = _≈_
  ; _≤_            = λ x y → x ≈ x ∧ y
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ {i} {j} i≈j → begin
                          i      ≈⟨ sym $ idem _ ⟩
                          i ∧ i  ≈⟨ ∧-cong refl i≈j ⟩
                          i ∧ j  ∎
      ; trans         = λ {i} {j} {k} i≈i∧j j≈j∧k → begin
                          i            ≈⟨ i≈i∧j ⟩
                          i ∧ j        ≈⟨ ∧-cong refl j≈j∧k ⟩
                          i ∧ (j ∧ k)  ≈⟨ sym (assoc _ _ _) ⟩
                          (i ∧ j) ∧ k  ≈⟨ ∧-cong (sym i≈i∧j) refl ⟩
                          i ∧ k        ∎
      }
    ; antisym = λ {x} {y} x≈x∧y y≈y∧x → begin
                  x      ≈⟨ x≈x∧y ⟩
                  x ∧ y  ≈⟨ comm _ _ ⟩
                  y ∧ x  ≈⟨ sym y≈y∧x ⟩
                  y      ∎
    }
  }

open Poset poset using (_≤_; isPartialOrder)

-- Every algebraic semilattice can be turned into an order-theoretic one.

isOrderTheoreticMeetSemilattice : R.IsMeetSemilattice _≈_ _≤_ _∧_
isOrderTheoreticMeetSemilattice = record
  { isPartialOrder = isPartialOrder
  ; infimum        = λ x y →
                       (begin
                         x ∧ y        ≈⟨ ∧-cong (sym (idem x)) refl ⟩
                         (x ∧ x) ∧ y  ≈⟨ assoc x x y  ⟩
                         x ∧ (x ∧ y)  ≈⟨ comm x (x ∧ y) ⟩
                         (x ∧ y) ∧ x  ∎) ,
                       (begin
                         x ∧ y        ≈⟨ ∧-cong refl (sym (idem y)) ⟩
                         x ∧ (y ∧ y)  ≈⟨ sym (assoc x y y) ⟩
                         (x ∧ y) ∧ y  ∎) ,
                       λ z z≈z∧x z≈z∧y → begin
                         z            ≈⟨ z≈z∧y ⟩
                         z ∧ y        ≈⟨ ∧-cong z≈z∧x refl ⟩
                         (z ∧ x) ∧ y  ≈⟨ assoc z x y ⟩
                         z ∧ (x ∧ y)  ∎
  }

orderTheoreticMeetSemilattice : R.MeetSemilattice _ _ _
orderTheoreticMeetSemilattice = record
  { isMeetSemilattice = isOrderTheoreticMeetSemilattice }

isOrderTheoreticJoinSemilattice : R.IsJoinSemilattice _≈_ (flip _≤_) _∧_
isOrderTheoreticJoinSemilattice = record
  { isPartialOrder = R.invIsPartialOrder poset
  ; supremum       = R.IsMeetSemilattice.infimum
                       isOrderTheoreticMeetSemilattice
  }

orderTheoreticJoinSemilattice : R.JoinSemilattice _ _ _
orderTheoreticJoinSemilattice = record
  { isJoinSemilattice = isOrderTheoreticJoinSemilattice }

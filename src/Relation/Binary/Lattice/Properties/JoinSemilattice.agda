------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by join semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.JoinSemilattice
  {c ℓ₁ ℓ₂} (J : JoinSemilattice c ℓ₁ ℓ₂) where

open JoinSemilattice J

import Algebra.Lattice as Alg
import Algebra.Structures as Alg
open import Algebra.Definitions _≈_
open import Algebra.Ordered.Structures using (IsPosemigroup)
open import Algebra.Ordered.Bundles using (Posemigroup)
open import Data.Product
open import Function.Base using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contraposition)

import Relation.Binary.Reasoning.PartialOrder as PoR

------------------------------------------------------------------------
-- Algebraic properties

-- The join operation is monotonic.

∨-monotonic : _∨_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
∨-monotonic {x} {y} {u} {v} x≤y u≤v =
  let _     , _     , least  = supremum x u
      y≤y∨v , v≤y∨v , _      = supremum y v
  in least (y ∨ v) (trans x≤y y≤y∨v) (trans u≤v v≤y∨v)

∨-cong : _∨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
∨-cong x≈y u≈v = antisym (∨-monotonic (reflexive x≈y) (reflexive u≈v))
                         (∨-monotonic (reflexive (Eq.sym x≈y))
                                      (reflexive (Eq.sym u≈v)))

-- The join operation is commutative, associative and idempotent.

∨-comm : Commutative _∨_
∨-comm x y =
  let x≤x∨y , y≤x∨y , least  = supremum x y
      y≤y∨x , x≤y∨x , least′ = supremum y x
  in antisym (least (y ∨ x) x≤y∨x y≤y∨x) (least′ (x ∨ y) y≤x∨y x≤x∨y)

∨-assoc : Associative _∨_
∨-assoc x y z =
  let x∨y≤[x∨y]∨z , z≤[x∨y]∨z   , least  = supremum (x ∨ y) z
      x≤x∨[y∨z]   , y∨z≤x∨[y∨z] , least′ = supremum x (y ∨ z)
      y≤y∨z       , z≤y∨z       , _      = supremum y z
      x≤x∨y       , y≤x∨y       , _      = supremum x y
  in antisym (least  (x ∨ (y ∨ z)) (∨-monotonic refl y≤y∨z)
                     (trans z≤y∨z y∨z≤x∨[y∨z]))
             (least′ ((x ∨ y) ∨ z) (trans x≤x∨y x∨y≤[x∨y]∨z)
                     (∨-monotonic y≤x∨y refl))

∨-idempotent : Idempotent _∨_
∨-idempotent x =
  let x≤x∨x , _ , least = supremum x x
  in antisym (least x refl refl) x≤x∨x

x≤y⇒x∨y≈y : ∀ {x y} → x ≤ y → x ∨ y ≈ y
x≤y⇒x∨y≈y {x} {y} x≤y = antisym
  (begin x ∨ y ≤⟨ ∨-monotonic x≤y refl ⟩
         y ∨ y ≈⟨ ∨-idempotent _ ⟩
         y ∎)
  (y≤x∨y _ _)
  where open PoR poset

-- Every order-theoretic semilattice can be turned into an algebraic one.

isAlgSemilattice : Alg.IsSemilattice _≈_ _∨_
isAlgSemilattice = record
  { isBand = record
    { isSemigroup = record
      { isMagma   = record
        { isEquivalence = isEquivalence
        ; ∙-cong        = ∨-cong
        }
      ; assoc  = ∨-assoc
      }
    ; idem     = ∨-idempotent
    }
  ; comm       = ∨-comm
  }

algSemilattice : Alg.Semilattice c ℓ₁
algSemilattice = record { isSemilattice = isAlgSemilattice }

-- Every semilattice gives rise to a posemigroup

isPosemigroup : IsPosemigroup _≈_ _≤_ _∨_
isPosemigroup = record
  { isPomagma        = record
    { isPartialOrder = isPartialOrder
    ; mono           = ∨-monotonic
    }
  ; assoc            = ∨-assoc
  }

posemigroup : Posemigroup c ℓ₁ ℓ₂
posemigroup = record
  { Carrier           = Carrier
  ; _≈_               = _≈_
  ; _≤_               = _≤_
  ; _∙_               = _∨_
  ; isPosemigroup     = isPosemigroup
  }

------------------------------------------------------------------------
-- The dual construction is a meet semilattice.

dualIsMeetSemilattice : IsMeetSemilattice _≈_ (flip _≤_) _∨_
dualIsMeetSemilattice = record
  { isPartialOrder = ≥-isPartialOrder
  ; infimum        = supremum
  }

dualMeetSemilattice : MeetSemilattice c ℓ₁ ℓ₂
dualMeetSemilattice = record
  { _∧_               = _∨_
  ; isMeetSemilattice = dualIsMeetSemilattice
  }

------------------------------------------------------------------------
-- If ≈ is decidable then so is ≤

≈-dec⇒≤-dec : Decidable _≈_ → Decidable _≤_
≈-dec⇒≤-dec _≟_ x y with (x ∨ y) ≟ y
... | yes x∨y≈y = yes (trans (x≤x∨y x y) (reflexive x∨y≈y))
... | no  x∨y≉y = no (contraposition x≤y⇒x∨y≈y x∨y≉y)

≈-dec⇒isDecPartialOrder : Decidable _≈_ → IsDecPartialOrder _≈_ _≤_
≈-dec⇒isDecPartialOrder _≟_ = record
  { isPartialOrder = isPartialOrder
  ; _≟_            = _≟_
  ; _≤?_           = ≈-dec⇒≤-dec _≟_
  }

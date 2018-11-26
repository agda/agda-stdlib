------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

-- The structures are parameterised by an equivalence relation

module Algebra.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.FunctionProperties _≈_
import Algebra.FunctionProperties.Consequences as Consequences
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Semigroups

record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong        : Congruent₂ ∙

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

record IsSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    assoc   : Associative ∙

  open IsMagma isMagma public

record IsBand (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    idem        : Idempotent ∙

  open IsSemigroup isSemigroup public

record IsSemilattice (∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isBand : IsBand ∧
    comm   : Commutative ∧

  open IsBand isBand public

------------------------------------------------------------------------
-- Monoids

record IsMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

record IsCommutativeMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identityˡ   : LeftIdentity ε ∙
    comm        : Commutative ∙

  open IsSemigroup isSemigroup public

  identityʳ : RightIdentity ε ∙
  identityʳ = Consequences.comm+idˡ⇒idʳ setoid comm identityˡ

  identity : Identity ε ∙
  identity = (identityˡ , identityʳ)

  isMonoid : IsMonoid ∙ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }

record IsIdempotentCommutativeMonoid (∙ : Op₂ A)
                                     (ε : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeMonoid : IsCommutativeMonoid ∙ ε
    idem                : Idempotent ∙

  open IsCommutativeMonoid isCommutativeMonoid public

------------------------------------------------------------------------
-- Groups

record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMonoid isMonoid public

  infixl 7 _-_
  _-_ : Op₂ A
  x - y = x ∙ (y ⁻¹)

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse

  uniqueˡ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
  uniqueˡ-⁻¹ = Consequences.assoc+id+invʳ⇒invˡ-unique
                setoid ∙-cong assoc identity inverseʳ

  uniqueʳ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
  uniqueʳ-⁻¹ = Consequences.assoc+id+invˡ⇒invʳ-unique
                setoid ∙-cong assoc identity inverseˡ

record IsAbelianGroup (∙ : Op₂ A)
                      (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = identityˡ
    ; comm        = comm
    }

------------------------------------------------------------------------
-- Semirings

record IsNearSemiring (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isMonoid    : IsMonoid + 0#
    *-isSemigroup : IsSemigroup *
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
    renaming
    ( assoc       to +-assoc
    ; ∙-cong      to +-cong
    ; identity    to +-identity
    ; identityˡ   to +-identityˡ
    ; identityʳ   to +-identityʳ
    ; isMagma     to +-isMagma
    ; isSemigroup to +-isSemigroup
    )

  open IsSemigroup *-isSemigroup public
    using ()
    renaming
    ( assoc    to *-assoc
    ; ∙-cong   to *-cong
    ; isMagma  to *-isMagma
    )

record IsSemiringWithoutOne (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isSemigroup         : IsSemigroup *
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsCommutativeMonoid +-isCommutativeMonoid public
    using ()
    renaming
    ( isMonoid    to +-isMonoid
    ; comm        to +-comm
    )

  open IsSemigroup *-isSemigroup public
    using ()
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    )

  zeroˡ : LeftZero 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# *
  zeroʳ = proj₂ zero

  isNearSemiring : IsNearSemiring + * 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribʳ      = proj₂ distrib
    ; zeroˡ         = zeroˡ
    }

  open IsNearSemiring isNearSemiring public
    hiding (+-isMonoid; zeroˡ)

record IsSemiringWithoutAnnihilatingZero (+ * : Op₂ A)
                                         (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isMonoid            : IsMonoid * 1#
    distrib               : * DistributesOver +

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  open IsCommutativeMonoid +-isCommutativeMonoid public
    renaming
    ( assoc       to +-assoc
    ; ∙-cong      to +-cong
    ; identity    to +-identity
    ; identityˡ   to +-identityˡ
    ; identityʳ   to +-identityʳ
    ; comm        to +-comm
    ; isMagma     to +-isMagma
    ; isSemigroup to +-isSemigroup
    ; isMonoid    to +-isMonoid
    )

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    )

record IsSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero + * 0# 1#
    zero : Zero 0# *

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
  isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isSemigroup         = *-isSemigroup
    ; distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
    using
    ( isNearSemiring
    ; zeroˡ
    ; zeroʳ
    )

record IsCommutativeSemiringWithoutOne
         (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
    *-comm               : Commutative *

  open IsSemiringWithoutOne isSemiringWithoutOne public

record IsCommutativeSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isCommutativeMonoid : IsCommutativeMonoid * 1#
    distribʳ              : * DistributesOverʳ +
    zeroˡ                 : LeftZero 0# *

  private
    module +-CM = IsCommutativeMonoid +-isCommutativeMonoid
    open module *-CM = IsCommutativeMonoid *-isCommutativeMonoid public
           using () renaming (comm to *-comm)

  distribˡ : * DistributesOverˡ +
  distribˡ = Consequences.comm+distrʳ⇒distrˡ
              +-CM.setoid +-CM.∙-cong *-comm distribʳ

  distrib : * DistributesOver +
  distrib = (distribˡ , distribʳ)

  zeroʳ : RightZero 0# *
  zeroʳ = Consequences.comm+zeˡ⇒zeʳ +-CM.setoid *-comm zeroˡ

  zero : Zero 0# *
  zero = (zeroˡ , zeroʳ)

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isMonoid            = *-CM.isMonoid
      ; distrib               = distrib
      }
    ; zero                    = zero
    }

  open IsSemiring isSemiring public
    hiding
    ( distrib; distribʳ; distribˡ
    ; zero; zeroˡ; zeroʳ
    ; +-isCommutativeMonoid
    )

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne + * 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm               = *-CM.comm
    }

------------------------------------------------------------------------
-- Rings

record IsRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isMonoid       : IsMonoid * 1#
    distrib          : * DistributesOver +

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc               to +-assoc
    ; ∙-cong              to +-cong
    ; identity            to +-identity
    ; identityˡ           to +-identityˡ
    ; identityʳ           to +-identityʳ
    ; inverse             to -‿inverse
    ; inverseˡ            to -‿inverseˡ
    ; inverseʳ            to -‿inverseʳ
    ; ⁻¹-cong             to -‿cong
    ; comm                to +-comm
    ; isMagma             to +-isMagma
    ; isSemigroup         to +-isSemigroup
    ; isMonoid            to +-isMonoid
    ; isCommutativeMonoid to +-isCommutativeMonoid
    ; isGroup             to +-isGroup
    )

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    )

  zeroˡ : LeftZero 0# *
  zeroˡ = Consequences.assoc+distribʳ+idʳ+invʳ⇒zeˡ setoid
           +-cong *-cong +-assoc (proj₂ distrib) +-identityʳ -‿inverseʳ

  zeroʳ : RightZero 0# *
  zeroʳ = Consequences.assoc+distribˡ+idʳ+invʳ⇒zeʳ setoid
           +-cong *-cong +-assoc (proj₁ distrib) +-identityʳ -‿inverseʳ

  zero : Zero 0# *
  zero = (zeroˡ , zeroʳ)

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero + * 0# 1#
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isMonoid            = *-isMonoid
    ; distrib               = distrib
    }

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    ; zero = zero
    }

  open IsSemiring isSemiring public
    using (distribˡ; distribʳ; isNearSemiring; isSemiringWithoutOne)

record IsCommutativeRing
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isRing : IsRing + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isCommutativeMonoid = record
      { isSemigroup = *-isSemigroup
      ; identityˡ   = *-identityˡ
      ; comm        = *-comm
      }
    ; distribʳ              = distribʳ
    ; zeroˡ                 = zeroˡ
    }

  open IsCommutativeSemiring isCommutativeSemiring public
    using
    ( *-isCommutativeMonoid
    ; isCommutativeSemiringWithoutOne
    )

------------------------------------------------------------------------
-- Lattices

record IsLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    ∨-isSemilattice : IsSemilattice ∨
    ∧-isSemilattice : IsSemilattice ∧
    absorptive      : Absorptive ∨ ∧

  ∨-absorbs-∧ : ∨ Absorbs ∧
  ∨-absorbs-∧ = proj₁ absorptive

  ∧-absorbs-∨ : ∧ Absorbs ∨
  ∧-absorbs-∨ = proj₂ absorptive

  open IsSemilattice ∨-isSemilattice public
    renaming
    ( ∙-cong      to ∨-cong
    ; assoc       to ∨-assoc
    ; comm        to ∨-comm
    ; idem        to ∨-idem
    ; isMagma     to ∨-isMagma
    ; isSemigroup to ∨-isSemigroup
    ; isBand      to ∨-isBand
    )

  open IsSemilattice ∧-isSemilattice public
    renaming
    ( ∙-cong      to ∧-cong
    ; assoc       to ∧-assoc
    ; comm        to ∧-comm
    ; idem        to ∧-idem
    ; isMagma     to ∧-isMagma
    ; isSemigroup to ∧-isSemigroup
    ; isBand      to ∧-isBand
    )
    hiding (refl; reflexive; sym; trans; isEquivalence; setoid)

record IsDistributiveLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isLattice    : IsLattice ∨ ∧
    ∨-∧-distribʳ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-cong                : Congruent₁ ¬

  open IsDistributiveLattice isDistributiveLattice public

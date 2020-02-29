------------------------------------------------------------------------
-- The Agda standard library
--
-- Ways to give instances of certain structures where some fields can
-- be given in terms of others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Structures.Biased
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- IsCommutativeMonoid

record IsCommutativeMonoidˡ (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identityˡ   : LeftIdentity ε ∙
    comm        : Commutative ∙

  open IsSemigroup isSemigroup

  private

    identityʳ : RightIdentity ε ∙
    identityʳ = Consequences.comm+idˡ⇒idʳ setoid comm identityˡ

    identity : Identity ε ∙
    identity = (identityˡ , identityʳ)

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = isSemigroup
      ; identity    = identity
      }
    ; comm = comm
    }

open IsCommutativeMonoidˡ public
  using () renaming (isCommutativeMonoid to isCommutativeMonoidˡ)


record IsCommutativeMonoidʳ (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identityʳ   : RightIdentity ε ∙
    comm        : Commutative ∙

  open IsSemigroup isSemigroup

  private

    identityˡ : LeftIdentity ε ∙
    identityˡ = Consequences.comm+idʳ⇒idˡ setoid comm identityʳ

    identity : Identity ε ∙
    identity = (identityˡ , identityʳ)

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = isSemigroup
      ; identity    = identity
      }
    ; comm = comm
    }

open IsCommutativeMonoidʳ public
  using () renaming (isCommutativeMonoid to isCommutativeMonoidʳ)


------------------------------------------------------------------------
-- IsCommutativeSemiring

record IsCommutativeSemiringˡ (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
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

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid = *-CM.isMonoid
        ; distrib = distrib
        }
      ; zero = zero
      }
    ; *-comm = *-comm
    }

open IsCommutativeSemiringˡ public
  using () renaming (isCommutativeSemiring to isCommutativeSemiringˡ)


record IsCommutativeSemiringʳ (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isCommutativeMonoid : IsCommutativeMonoid * 1#
    distribˡ              : * DistributesOverˡ +
    zeroʳ                 : RightZero 0# *

  private
    module +-CM = IsCommutativeMonoid +-isCommutativeMonoid
    open module *-CM = IsCommutativeMonoid *-isCommutativeMonoid public
           using () renaming (comm to *-comm)

    distribʳ : * DistributesOverʳ +
    distribʳ = Consequences.comm+distrˡ⇒distrʳ
                +-CM.setoid +-CM.∙-cong *-comm distribˡ

    distrib : * DistributesOver +
    distrib = (distribˡ , distribʳ)

    zeroˡ : LeftZero 0# *
    zeroˡ = Consequences.comm+zeʳ⇒zeˡ +-CM.setoid *-comm zeroʳ

    zero : Zero 0# *
    zero = (zeroˡ , zeroʳ)

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid = *-CM.isMonoid
        ; distrib = distrib
        }
      ; zero = zero
      }
    ; *-comm = *-comm
    }

open IsCommutativeSemiringʳ public
  using () renaming (isCommutativeSemiring to isCommutativeSemiringʳ)


------------------------------------------------------------------------
-- IsRing

-- We can recover a ring without proving that 0# annihilates *.
record IsRingWithoutAnnihilatingZero (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
                                     : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isMonoid       : IsMonoid * 1#
    distrib          : * DistributesOver +

  private

    module + = IsAbelianGroup +-isAbelianGroup
    module * = IsMonoid *-isMonoid

    open + using (setoid) renaming (∙-cong to +-cong)
    open * using ()       renaming (∙-cong to *-cong)

    zeroˡ : LeftZero 0# *
    zeroˡ = Consequences.assoc+distribʳ+idʳ+invʳ⇒zeˡ setoid
             +-cong *-cong +.assoc (proj₂ distrib) +.identityʳ +.inverseʳ

    zeroʳ : RightZero 0# *
    zeroʳ = Consequences.assoc+distribˡ+idʳ+invʳ⇒zeʳ setoid
             +-cong *-cong +.assoc (proj₁ distrib) +.identityʳ +.inverseʳ

    zero : Zero 0# *
    zero = (zeroˡ , zeroʳ)

  isRing : IsRing + * -_ 0# 1#
  isRing = record
    { +-isAbelianGroup = +-isAbelianGroup
    ; *-isMonoid = *-isMonoid
    ; distrib = distrib
    ; zero = zero
    }

open IsRingWithoutAnnihilatingZero public
  using () renaming (isRing to isRingWithoutAnnihilatingZero)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Ways to give instances of certain structures where some fields can
-- be given in terms of others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Consequences.Setoid
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Structures.Biased
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Definitions _≈_
open import Algebra.Structures  _≈_

------------------------------------------------------------------------
-- IsCommutativeMonoid

record IsCommutativeMonoidˡ (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identityˡ   : LeftIdentity ε ∙
    comm        : Commutative ∙

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = isSemigroup
      ; identity    = comm+idˡ⇒id setoid comm identityˡ
      }
    ; comm = comm
    } where open IsSemigroup isSemigroup

open IsCommutativeMonoidˡ public
  using () renaming (isCommutativeMonoid to isCommutativeMonoidˡ)


record IsCommutativeMonoidʳ (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identityʳ   : RightIdentity ε ∙
    comm        : Commutative ∙

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = isSemigroup
      ; identity    = comm+idʳ⇒id setoid comm identityʳ
      }
    ; comm = comm
    } where open IsSemigroup isSemigroup

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

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-cong                = *.∙-cong
        ; *-assoc               = *.assoc
        ; *-identity            = *.identity
        ; distrib               = comm+distrʳ⇒distr +.setoid +.∙-cong *.comm distribʳ
        }
      ; zero = comm+zeˡ⇒ze +.setoid *.comm zeroˡ
      }
    ; *-comm = *.comm
    }
    where
    module + = IsCommutativeMonoid +-isCommutativeMonoid
    module * = IsCommutativeMonoid *-isCommutativeMonoid

open IsCommutativeSemiringˡ public
  using () renaming (isCommutativeSemiring to isCommutativeSemiringˡ)


record IsCommutativeSemiringʳ (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isCommutativeMonoid : IsCommutativeMonoid * 1#
    distribˡ              : * DistributesOverˡ +
    zeroʳ                 : RightZero 0# *

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-cong                = *.∙-cong
        ; *-assoc               = *.assoc
        ; *-identity            = *.identity
        ; distrib               = comm+distrˡ⇒distr +.setoid +.∙-cong *.comm distribˡ
        }
      ; zero = comm+zeʳ⇒ze +.setoid *.comm zeroʳ
      }
    ; *-comm = *.comm
    }
    where
    module + = IsCommutativeMonoid +-isCommutativeMonoid
    module * = IsCommutativeMonoid *-isCommutativeMonoid

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

  module + = IsAbelianGroup +-isAbelianGroup
  module * = IsMonoid *-isMonoid

  open + using (setoid) renaming (∙-cong to +-cong)
  open * using ()       renaming (∙-cong to *-cong)

  zeroˡ : LeftZero 0# *
  zeroˡ = assoc+distribʳ+idʳ+invʳ⇒zeˡ setoid
            +-cong *-cong +.assoc (proj₂ distrib) +.identityʳ +.inverseʳ

  zeroʳ : RightZero 0# *
  zeroʳ = assoc+distribˡ+idʳ+invʳ⇒zeʳ setoid
            +-cong *-cong +.assoc (proj₁ distrib) +.identityʳ +.inverseʳ

  zero : Zero 0# *
  zero = (zeroˡ , zeroʳ)

  isRing : IsRing + * -_ 0# 1#
  isRing = record
    { +-isAbelianGroup = +-isAbelianGroup
    ; *-isMonoid       = *-isMonoid
    ; distrib          = distrib
    ; zero             = zero
    }

open IsRingWithoutAnnihilatingZero public
  using () renaming (isRing to isRingWithoutAnnihilatingZero)

------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Structures with 1 unary operation & 1 element
------------------------------------------------------------------------

record IsSuccessorSet (suc# : Op₁ A) (zero# : A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    suc#-cong     : Congruent₁ suc#

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

------------------------------------------------------------------------
-- Structures with 1 binary operation
------------------------------------------------------------------------

record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong        : Congruent₂ ∙

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

  ∙-congˡ : LeftCongruent ∙
  ∙-congˡ y≈z = ∙-cong refl y≈z

  ∙-congʳ : RightCongruent ∙
  ∙-congʳ y≈z = ∙-cong y≈z refl


record IsCommutativeMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    comm    : Commutative ∙

  open IsMagma isMagma public

record IsIdempotentMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    idem    : Idempotent ∙

  open IsMagma isMagma public

record IsAlternativeMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    alter    : Alternative ∙

  open IsMagma isMagma public

  alternativeˡ : LeftAlternative ∙
  alternativeˡ = proj₁ alter

  alternativeʳ : RightAlternative ∙
  alternativeʳ = proj₂ alter

record IsFlexibleMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    flex     : Flexible ∙

  open IsMagma isMagma public

record IsMedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    medial  : Medial ∙

  open IsMagma isMagma public

record IsSemimedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma    : IsMagma ∙
    semiMedial : Semimedial ∙

  open IsMagma isMagma public

  semimedialˡ : LeftSemimedial ∙
  semimedialˡ = proj₁ semiMedial

  semimedialʳ : RightSemimedial ∙
  semimedialʳ = proj₂ semiMedial

record IsSelectiveMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    sel     : Selective ∙

  open IsMagma isMagma public


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


record IsCommutativeSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    comm        : Commutative ∙

  open IsSemigroup isSemigroup public

  isCommutativeMagma : IsCommutativeMagma ∙
  isCommutativeMagma = record
    { isMagma = isMagma
    ; comm    = comm
    }

------------------------------------------------------------------------
-- Structures with 1 binary operation & 1 element
------------------------------------------------------------------------

record IsUnitalMagma (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    identity : Identity ε ∙

  open IsMagma isMagma public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity


record IsMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

  isUnitalMagma : IsUnitalMagma ∙ ε
  isUnitalMagma = record
    { isMagma  = isMagma
    ; identity = identity
    }


record IsCommutativeMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMonoid : IsMonoid ∙ ε
    comm     : Commutative ∙

  open IsMonoid isMonoid public

  isCommutativeSemigroup : IsCommutativeSemigroup ∙
  isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm        = comm
    }

  open IsCommutativeSemigroup isCommutativeSemigroup public
    using (isCommutativeMagma)


record IsIdempotentCommutativeMonoid (∙ : Op₂ A)
                                     (ε : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeMonoid : IsCommutativeMonoid ∙ ε
    idem                : Idempotent ∙

  open IsCommutativeMonoid isCommutativeMonoid public

  isBand : IsBand ∙
  isBand = record { isSemigroup = isSemigroup ; idem = idem }


------------------------------------------------------------------------
-- Structures with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsInvertibleMagma (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma _∙_
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMagma isMagma public

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse


record IsInvertibleUnitalMagma (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isInvertibleMagma : IsInvertibleMagma _∙_  ε ⁻¹
    identity          : Identity ε _∙_

  open IsInvertibleMagma isInvertibleMagma public

  identityˡ : LeftIdentity ε _∙_
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε _∙_
  identityʳ = proj₂ identity

  isUnitalMagma : IsUnitalMagma _∙_  ε
  isUnitalMagma = record
    { isMagma  = isMagma
    ; identity = identity
    }


record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMonoid isMonoid public

  infixr 6 _\\_
  _\\_ : Op₂ A
  x \\ y = (x ⁻¹) ∙ y

  infixl 6 _//_
  _//_ : Op₂ A
  x // y = x ∙ (y ⁻¹)

  -- Deprecated.
  infixl 6 _-_
  _-_ : Op₂ A
  _-_ = _//_
  {-# WARNING_ON_USAGE _-_
  "Warning: _-_ was deprecated in v2.1.
  Please use _//_ instead. "
  #-}

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse

  uniqueˡ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
  uniqueˡ-⁻¹ = Consequences.assoc∧id∧invʳ⇒invˡ-unique
                setoid ∙-cong assoc identity inverseʳ

  uniqueʳ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
  uniqueʳ-⁻¹ = Consequences.assoc∧id∧invˡ⇒invʳ-unique
                setoid ∙-cong assoc identity inverseˡ

  isInvertibleMagma : IsInvertibleMagma _∙_ ε _⁻¹
  isInvertibleMagma = record
    { isMagma = isMagma
    ; inverse = inverse
    ; ⁻¹-cong = ⁻¹-cong
    }

  isInvertibleUnitalMagma : IsInvertibleUnitalMagma _∙_ ε _⁻¹
  isInvertibleUnitalMagma = record
    { isInvertibleMagma = isInvertibleMagma
    ; identity = identity
    }


record IsAbelianGroup (∙ : Op₂ A)
                      (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public renaming (_//_ to _-_) hiding (_\\_; _-_)

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeMagma; isCommutativeSemigroup)


------------------------------------------------------------------------
-- Structures with 2 binary operations & 1 element
------------------------------------------------------------------------

record IsNearSemiring (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isMonoid    : IsMonoid + 0#
    *-cong        : Congruent₂ *
    *-assoc       : Associative *
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
    renaming
    ( assoc         to +-assoc
    ; ∙-cong        to +-cong
    ; ∙-congˡ       to +-congˡ
    ; ∙-congʳ       to +-congʳ
    ; identity      to +-identity
    ; identityˡ     to +-identityˡ
    ; identityʳ     to +-identityʳ
    ; isMagma       to +-isMagma
    ; isUnitalMagma to +-isUnitalMagma
    ; isSemigroup   to +-isSemigroup
    )

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-isSemigroup : IsSemigroup *
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc   = *-assoc
    }

  open IsMagma *-isMagma public
    using ()
    renaming
    ( ∙-congˡ  to *-congˡ
    ; ∙-congʳ  to *-congʳ
    )


record IsSemiringWithoutOne (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-cong                : Congruent₂ *
    *-assoc               : Associative *
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsCommutativeMonoid +-isCommutativeMonoid public
    using (setoid)
    renaming
    ( comm                   to +-comm
    ; isMonoid               to +-isMonoid
    ; isCommutativeMagma     to +-isCommutativeMagma
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    )

  open Setoid setoid public

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-isSemigroup : IsSemigroup *
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc   = *-assoc
    }

  open IsMagma *-isMagma public
    using ()
    renaming
    ( ∙-congˡ to *-congˡ
    ; ∙-congʳ to *-congʳ
    )

  zeroˡ : LeftZero 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# *
  zeroʳ = proj₂ zero

  isNearSemiring : IsNearSemiring + * 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-cong        = *-cong
    ; *-assoc       = *-assoc
    ; distribʳ      = proj₂ distrib
    ; zeroˡ         = zeroˡ
    }

record IsCommutativeSemiringWithoutOne
         (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
    *-comm               : Commutative *

  open IsSemiringWithoutOne isSemiringWithoutOne public

  *-isCommutativeSemigroup : IsCommutativeSemigroup *
  *-isCommutativeSemigroup = record
    { isSemigroup = *-isSemigroup
    ; comm        = *-comm
    }

  open IsCommutativeSemigroup *-isCommutativeSemigroup public
    using () renaming (isCommutativeMagma to *-isCommutativeMagma)

------------------------------------------------------------------------
-- Structures with 2 binary operations & 2 elements
------------------------------------------------------------------------

record IsSemiringWithoutAnnihilatingZero (+ * : Op₂ A)
                                         (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-cong                : Congruent₂ *
    *-assoc               : Associative *
    *-identity            : Identity 1# *
    distrib               : * DistributesOver +

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  open IsCommutativeMonoid +-isCommutativeMonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isUnitalMagma          to +-isUnitalMagma
    ; isCommutativeMagma     to +-isCommutativeMagma
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    )

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-isSemigroup : IsSemigroup *
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc   = *-assoc
    }

  *-isMonoid : IsMonoid * 1#
  *-isMonoid = record
    { isSemigroup = *-isSemigroup
    ; identity    = *-identity
    }

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
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
    ; *-cong                = *-cong
    ; *-assoc               = *-assoc
    ; distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
    using
    ( isNearSemiring
    ; zeroˡ
    ; zeroʳ
    )


record IsCommutativeSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isSemiring : IsSemiring + * 0# 1#
    *-comm     : Commutative *

  open IsSemiring isSemiring public

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne + * 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm = *-comm
    }

  open IsCommutativeSemiringWithoutOne isCommutativeSemiringWithoutOne public
    using
    ( *-isCommutativeMagma
    ; *-isCommutativeSemigroup
    )

  *-isCommutativeMonoid : IsCommutativeMonoid * 1#
  *-isCommutativeMonoid = record
    { isMonoid = *-isMonoid
    ; comm     = *-comm
    }


record IsCancellativeCommutativeSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
    *-cancelˡ-nonZero     : AlmostLeftCancellative 0# *

  open IsCommutativeSemiring isCommutativeSemiring public

  *-cancelʳ-nonZero : AlmostRightCancellative 0# *
  *-cancelʳ-nonZero = Consequences.comm∧almostCancelˡ⇒almostCancelʳ setoid
      *-comm *-cancelˡ-nonZero

record IsIdempotentSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isSemiring     : IsSemiring + * 0# 1#
    +-idem         : Idempotent +

  open IsSemiring isSemiring public

record IsKleeneAlgebra (+ * : Op₂ A) (⋆ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isIdempotentSemiring  : IsIdempotentSemiring + * 0# 1#
    starExpansive         : StarExpansive 1# + * ⋆
    starDestructive       : StarDestructive + * ⋆

  open IsIdempotentSemiring isIdempotentSemiring public

  starExpansiveˡ : StarLeftExpansive 1# + * ⋆
  starExpansiveˡ = proj₁ starExpansive

  starExpansiveʳ : StarRightExpansive 1# + * ⋆
  starExpansiveʳ = proj₂ starExpansive

  starDestructiveˡ : StarLeftDestructive + * ⋆
  starDestructiveˡ = proj₁ starDestructive

  starDestructiveʳ : StarRightDestructive + * ⋆
  starDestructiveʳ = proj₂ starDestructive

record IsQuasiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isMonoid    : IsMonoid + 0#
    *-cong        : Congruent₂ *
    *-assoc       : Associative *
    *-identity    : Identity 1# *
    distrib       : * DistributesOver +
    zero          : Zero 0# *

  open IsMonoid +-isMonoid public
    renaming
    ( assoc         to +-assoc
    ; ∙-cong        to +-cong
    ; ∙-congˡ       to +-congˡ
    ; ∙-congʳ       to +-congʳ
    ; identity      to +-identity
    ; identityˡ     to +-identityˡ
    ; identityʳ     to +-identityʳ
    ; isMagma       to +-isMagma
    ; isUnitalMagma to +-isUnitalMagma
    ; isSemigroup   to +-isSemigroup
    )

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  zeroˡ : LeftZero 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# *
  zeroʳ = proj₂ zero

  identityˡ : LeftIdentity 1# *
  identityˡ = proj₁ *-identity

  identityʳ : RightIdentity 1# *
  identityʳ = proj₂ *-identity

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-isSemigroup : IsSemigroup *
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc   = *-assoc
    }

  *-isMonoid : IsMonoid * 1#
  *-isMonoid = record
    { isSemigroup = *-isSemigroup
    ; identity    = *-identity
    }

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    )

------------------------------------------------------------------------
-- Structures with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsRingWithoutOne (+ * : Op₂ A) (-_ : Op₁ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-cong           : Congruent₂ *
    *-assoc          : Associative *
    distrib          : * DistributesOver +

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                   to +-assoc
    ; ∙-cong                  to +-cong
    ; ∙-congˡ                 to +-congˡ
    ; ∙-congʳ                 to +-congʳ
    ; identity                to +-identity
    ; identityˡ               to +-identityˡ
    ; identityʳ               to +-identityʳ
    ; inverse                 to -‿inverse
    ; inverseˡ                to -‿inverseˡ
    ; inverseʳ                to -‿inverseʳ
    ; ⁻¹-cong                 to -‿cong
    ; comm                    to +-comm
    ; isMagma                 to +-isMagma
    ; isSemigroup             to +-isSemigroup
    ; isMonoid                to +-isMonoid
    ; isUnitalMagma           to +-isUnitalMagma
    ; isCommutativeMagma      to +-isCommutativeMagma
    ; isCommutativeMonoid     to +-isCommutativeMonoid
    ; isCommutativeSemigroup  to +-isCommutativeSemigroup
    ; isInvertibleMagma       to +-isInvertibleMagma
    ; isInvertibleUnitalMagma to +-isInvertibleUnitalMagma
    ; isGroup                 to +-isGroup
    )

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  zeroˡ : LeftZero 0# *
  zeroˡ = Consequences.assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ setoid
    +-cong *-cong +-assoc distribʳ +-identityʳ -‿inverseʳ

  zeroʳ : RightZero 0# *
  zeroʳ = Consequences.assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ setoid
    +-cong *-cong +-assoc distribˡ +-identityʳ -‿inverseʳ

  zero : Zero 0# *
  zero = zeroˡ , zeroʳ

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-isSemigroup : IsSemigroup *
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc   = *-assoc
    }

  open IsSemigroup *-isSemigroup public
    using ()
    renaming
    ( ∙-congˡ   to *-congˡ
    ; ∙-congʳ   to *-congʳ
    )

------------------------------------------------------------------------
-- Structures with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record IsNonAssociativeRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-cong           : Congruent₂ *
    *-identity       : Identity 1# *
    distrib          : * DistributesOver +
    zero             : Zero 0# *

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                   to +-assoc
    ; ∙-cong                  to +-cong
    ; ∙-congˡ                 to +-congˡ
    ; ∙-congʳ                 to +-congʳ
    ; identity                to +-identity
    ; identityˡ               to +-identityˡ
    ; identityʳ               to +-identityʳ
    ; inverse                 to -‿inverse
    ; inverseˡ                to -‿inverseˡ
    ; inverseʳ                to -‿inverseʳ
    ; ⁻¹-cong                 to -‿cong
    ; comm                    to +-comm
    ; isMagma                 to +-isMagma
    ; isSemigroup             to +-isSemigroup
    ; isMonoid                to +-isMonoid
    ; isUnitalMagma           to +-isUnitalMagma
    ; isCommutativeMagma      to +-isCommutativeMagma
    ; isCommutativeMonoid     to +-isCommutativeMonoid
    ; isCommutativeSemigroup  to +-isCommutativeSemigroup
    ; isInvertibleMagma       to +-isInvertibleMagma
    ; isInvertibleUnitalMagma to +-isInvertibleUnitalMagma
    ; isGroup                 to +-isGroup
    )

  zeroˡ : LeftZero 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# *
  zeroʳ = proj₂ zero

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-identityˡ : LeftIdentity 1# *
  *-identityˡ = proj₁ *-identity

  *-identityʳ : RightIdentity 1# *
  *-identityʳ = proj₂ *-identity

  *-isUnitalMagma : IsUnitalMagma * 1#
  *-isUnitalMagma = record
    { isMagma = *-isMagma
    ; identity = *-identity
    }

  open IsUnitalMagma *-isUnitalMagma public
    using ()
    renaming
    ( ∙-congˡ   to *-congˡ
    ; ∙-congʳ   to *-congʳ
    )

record IsNearring (+ * : Op₂ A) (0# 1# : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isQuasiring : IsQuasiring + * 0# 1#
    +-inverse   : Inverse 0# _⁻¹ +
    ⁻¹-cong     : Congruent₁ _⁻¹

  open IsQuasiring isQuasiring public

  +-inverseˡ : LeftInverse 0# _⁻¹ +
  +-inverseˡ = proj₁ +-inverse

  +-inverseʳ : RightInverse 0# _⁻¹ +
  +-inverseʳ = proj₂ +-inverse

record IsRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-cong           : Congruent₂ *
    *-assoc          : Associative *
    *-identity       : Identity 1# *
    distrib          : * DistributesOver +

  isRingWithoutOne : IsRingWithoutOne + * -_ 0#
  isRingWithoutOne = record
    { +-isAbelianGroup = +-isAbelianGroup
    ; *-cong  = *-cong
    ; *-assoc = *-assoc
    ; distrib = distrib
    }

  open IsRingWithoutOne isRingWithoutOne public
    hiding (+-isAbelianGroup; *-cong; *-assoc; distrib)

  *-isMonoid : IsMonoid * 1#
  *-isMonoid = record
    { isSemigroup = *-isSemigroup
    ; identity    = *-identity
    }

  open IsMonoid *-isMonoid public
    using ()
    renaming
    ( identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    )

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero + * 0# 1#
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-cong                = *-cong
    ; *-assoc               = *-assoc
    ; *-identity            = *-identity
    ; distrib               = distrib
    }

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    ; zero = zero
    }

  open IsSemiring isSemiring public
    using (isNearSemiring; isSemiringWithoutOne)


record IsCommutativeRing
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isRing : IsRing + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = isSemiring
    ; *-comm = *-comm
    }

  open IsCommutativeSemiring isCommutativeSemiring public
    using
    ( isCommutativeSemiringWithoutOne
    ; *-isCommutativeMagma
    ; *-isCommutativeSemigroup
    ; *-isCommutativeMonoid
    )

------------------------------------------------------------------------
-- Structures with 3 binary operations
------------------------------------------------------------------------

record IsQuasigroup (∙ \\ // : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma       : IsMagma ∙
    \\-cong       : Congruent₂ \\
    //-cong       : Congruent₂ //
    leftDivides   : LeftDivides ∙ \\
    rightDivides  : RightDivides ∙ //

  open IsMagma isMagma public

  \\-congˡ : LeftCongruent \\
  \\-congˡ y≈z = \\-cong refl y≈z

  \\-congʳ : RightCongruent \\
  \\-congʳ y≈z = \\-cong y≈z refl

  //-congˡ : LeftCongruent //
  //-congˡ y≈z = //-cong refl y≈z

  //-congʳ : RightCongruent //
  //-congʳ y≈z = //-cong y≈z refl

  leftDividesˡ : LeftDividesˡ ∙ \\
  leftDividesˡ = proj₁ leftDivides

  leftDividesʳ : LeftDividesʳ ∙ \\
  leftDividesʳ = proj₂ leftDivides

  rightDividesˡ : RightDividesˡ ∙ //
  rightDividesˡ = proj₁ rightDivides

  rightDividesʳ : RightDividesʳ ∙ //
  rightDividesʳ = proj₂ rightDivides


record IsLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isQuasigroup : IsQuasigroup ∙ \\ //
    identity     : Identity ε ∙

  open IsQuasigroup isQuasigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

record IsLeftBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop  : IsLoop ∙ \\ //  ε
    leftBol : LeftBol ∙

  open IsLoop isLoop public

record IsRightBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop   : IsLoop ∙ \\ //  ε
    rightBol : RightBol ∙

  open IsLoop isLoop public

record IsMoufangLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLeftBolLoop  : IsLeftBolLoop ∙ \\ //  ε
    rightBol       : RightBol ∙
    identical      : Identical ∙

  open IsLeftBolLoop isLeftBolLoop public

record IsMiddleBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop    : IsLoop ∙ \\ //  ε
    middleBol : MiddleBol ∙ \\ //

  open IsLoop isLoop public

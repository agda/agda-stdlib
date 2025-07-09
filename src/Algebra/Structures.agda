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

-- The file now re-exports structures defined in their own submodules,
-- grouped 'logically' by elaborations on a basic Raw signature, with
-- some additional redundancy for the sake of existing conventions,
-- eg. `IsMagma` and `IsSemigroup` share the same `Raw` signature, but
-- are differentiated because they enjoy different `Properties`.
-- This may change in subsequent revisions!

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Re-exports

open import Algebra.Structures.IsSuccessorSet _≈_ public
open import Algebra.Structures.IsMagma _≈_ public
open import Algebra.Structures.IsSemigroup _≈_ public
open import Algebra.Structures.IsMonoid _≈_ public
open import Algebra.Structures.IsQuasigroup _≈_ public
open import Algebra.Structures.IsGroup _≈_ public

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
    using (setoid; isEquivalence)
    renaming
    ( ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; assoc                  to +-assoc
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMonoid               to +-isMonoid
    ; isCommutativeMagma     to +-isCommutativeMagma
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    )

  open IsEquivalence isEquivalence public

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

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

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

  +-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid + 0#
  +-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = +-isCommutativeMonoid
    ; idem = +-idem
    }

  open IsIdempotentCommutativeMonoid +-isIdempotentCommutativeMonoid public
    using ()
    renaming ( isCommutativeBand to +-isCommutativeBand
             ; isBand to +-isBand
             ; isIdempotentMonoid to +-isIdempotentMonoid
             )


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

  isNearSemiring : IsNearSemiring + * 0#
  isNearSemiring = record
    { +-isMonoid = +-isMonoid
    ; *-cong = *-cong
    ; *-assoc = *-assoc
    ; distribʳ = distribʳ
    ; zeroˡ = zeroˡ
    }

  open IsNearSemiring isNearSemiring public
    using (*-isMagma; *-isSemigroup; *-congˡ; *-congʳ)

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
    using (isSemiringWithoutOne)


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

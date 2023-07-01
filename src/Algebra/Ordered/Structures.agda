------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≤_ : Rel A ℓ₂)       -- The order
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Data.Product.Base using (proj₁; proj₂)
open import Function.Base using (flip)
open import Level using (_⊔_)
open import Relation.Binary.Definitions using (Transitive; Monotonic₁; Monotonic₂)
open import Relation.Binary.Structures using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Consequences using (mono₂⇒cong₂)

------------------------------------------------------------------------
-- Preordered structures

-- Preordered magmas (promagmas)

record IsPromagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder  : IsPreorder _≈_ _≤_
    ∙-cong      : Congruent₂ ∙
    mono        : Monotonic₂ _≤_ _≤_ _≤_ ∙

  open IsPreorder isPreorder public

  mono₁ : ∀ {x} → Monotonic₁ _≤_ _≤_ (flip ∙ x)
  mono₁ y≈z = mono y≈z refl

  mono₂ : ∀ {x} → Monotonic₁ _≤_ _≤_ (∙ x)
  mono₂ y≈z = mono refl y≈z

  isMagma : IsMagma ∙
  isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

  open IsMagma isMagma public using (setoid; ∙-congˡ; ∙-congʳ)

-- Preordered semigroups (prosemigroups)

record IsProsemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma  : IsPromagma ∙
    assoc       : Associative ∙

  open IsPromagma isPromagma public

  isSemigroup : IsSemigroup ∙
  isSemigroup = record { isMagma = isMagma ; assoc = assoc }

-- Preordered monoids (promonoids)

record IsPromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    identity       : Identity ε ∙

  open IsProsemigroup isProsemigroup public

  isMonoid : IsMonoid ∙ ε
  isMonoid = record { isSemigroup = isSemigroup ; identity = identity }

  open IsMonoid isMonoid public using (identityˡ; identityʳ)

-- Preordered commutative monoids (commutative promonoids)

record IsCommutativePromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    comm        : Commutative ∙

  open IsPromonoid isPromonoid public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeSemigroup)

-- Preordered semirings (prosemirings)

record IsProsemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePromonoid : IsCommutativePromonoid + 0#
    *-cong                   : Congruent₂ *
    *-mono                   : Monotonic₂ _≤_ _≤_ _≤_ *
    *-assoc                  : Associative *
    *-identity               : Identity 1# *
    distrib                  : * DistributesOver +
    zero                     : Zero 0# *

  open IsCommutativePromonoid +-isCommutativePromonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; mono₁                  to +-mono₁
    ; mono₂                  to +-mono₂
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    )

  *-isPromonoid : IsPromonoid * 1#
  *-isPromonoid = record
    { isProsemigroup = record
      { isPromagma   = record
        { isPreorder = isPreorder
        ; ∙-cong     = *-cong
        ; mono       = *-mono
        }
      ; assoc        = *-assoc
      }
    ; identity       = *-identity
    }

  open IsPromonoid *-isPromonoid public
    using ()
    renaming
    ( ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; mono₁       to *-mono₁
    ; mono₂       to *-mono₂
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    ; isMonoid    to *-isMonoid
    )

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid           = +-isCommutativeMonoid
      ; *-cong                          = *-cong
      ; *-assoc                         = *-assoc
      ; *-identity                      = *-identity
      ; distrib                         = distrib
      }
    ; zero                              = zero
    }

  open IsSemiring isSemiring public using (distribˡ; distribʳ; zeroˡ; zeroʳ)

-- Preordered IdempotentSemiring (IdempotentProsemiring)

record IsIdempotentProsemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemiring  : IsProsemiring + * 0# 1#
    +-idem         : Idempotent +

  open IsProsemiring isProsemiring public

  isIdempotentSemiring : IsIdempotentSemiring + * 0# 1#
  isIdempotentSemiring = record { isSemiring = isSemiring ; +-idem = +-idem }

  open IsIdempotentSemiring isIdempotentSemiring public using (+-idem)

-- Preordered KleeneAlgebra (proKleeneAlgebra)

record IsProKleeneAlgebra (+ * : Op₂ A) (⋆ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isIdempotentProsemiring : IsIdempotentProsemiring + * 0# 1#
    starExpansive           : StarExpansive 1# + * ⋆
    starDestructive         : StarDestructive + * ⋆

  open IsIdempotentProsemiring isIdempotentProsemiring public

  isKleeneAlgebra : IsKleeneAlgebra + * ⋆ 0# 1#
  isKleeneAlgebra = record
    { isIdempotentSemiring = isIdempotentSemiring
    ; starExpansive        = starExpansive
    ; starDestructive      = starDestructive
    }

  open IsKleeneAlgebra isKleeneAlgebra public using (starExpansive; starDestructive)

------------------------------------------------------------------------
-- Partially ordered structures

-- Partially ordered magmas (pomagmas)

record IsPomagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    mono           : Monotonic₂ _≤_ _≤_ _≤_ ∙

  open IsPartialOrder isPartialOrder public

  ∙-cong : Congruent₂ ∙
  ∙-cong = mono₂⇒cong₂ _≈_ _≈_ Eq.sym reflexive antisym mono

  isPromagma : IsPromagma ∙
  isPromagma = record
    { isPreorder = isPreorder
    ; ∙-cong     = ∙-cong
    ; mono       = mono
    }

  open IsPromagma isPromagma public
    using (setoid; ∙-congˡ; ∙-congʳ; mono₁; mono₂; isMagma)

-- Partially ordered semigroups (posemigroups)

record IsPosemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma : IsPomagma ∙
    assoc     : Associative ∙

  open IsPomagma isPomagma public

  isProsemigroup : IsProsemigroup ∙
  isProsemigroup = record { isPromagma = isPromagma ; assoc = assoc }

  open IsProsemigroup isProsemigroup public using (isSemigroup)

-- Partially ordered monoids (pomonoids)

record IsPomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    identity      : Identity ε ∙

  open IsPosemigroup isPosemigroup public

  isPromonoid : IsPromonoid ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

  open IsPromonoid isPromonoid public
    using (isMonoid; identityˡ; identityʳ)

-- Partially ordered commutative monoids (commutative pomonoids)

record IsCommutativePomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    comm       : Commutative ∙

  open IsPomonoid isPomonoid public

  isCommutativePromonoid : IsCommutativePromonoid ∙ ε
  isCommutativePromonoid = record { isPromonoid = isPromonoid ; comm = comm }

  open IsCommutativePromonoid isCommutativePromonoid public
    using (isCommutativeMonoid; isCommutativeSemigroup)

-- Partially ordered semirings (posemirings)

record IsPosemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePomonoid : IsCommutativePomonoid + 0#
    *-mono                  : Monotonic₂ _≤_ _≤_ _≤_ *
    *-assoc                 : Associative *
    *-identity              : Identity 1# *
    distrib                 : * DistributesOver +
    zero                    : Zero 0# *

  open IsCommutativePomonoid +-isCommutativePomonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; mono₁                  to +-mono₁
    ; mono₂                  to +-mono₂
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isPromagma             to +-isPromagma
    ; isPomagma              to +-isPomagma
    ; isSemigroup            to +-isSemigroup
    ; isProsemigroup         to +-isProsemigroup
    ; isPosemigroup          to +-isPosemigroup
    ; isMonoid               to +-isMonoid
    ; isPromonoid            to +-isPromonoid
    ; isPomonoid             to +-isPomonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativePromonoid to +-isCommutativePromonoid
    )

  *-isPomonoid : IsPomonoid * 1#
  *-isPomonoid = record
    { isPosemigroup      = record
      { isPomagma        = record
        { isPartialOrder = isPartialOrder
        ; mono           = *-mono
        }
      ; assoc            = *-assoc
      }
    ; identity           = *-identity
    }

  open IsPomonoid *-isPomonoid public
    using ()
    renaming
    ( ∙-cong         to *-cong
    ; ∙-congˡ        to *-congˡ
    ; ∙-congʳ        to *-congʳ
    ; mono₁          to *-mono₁
    ; mono₂          to *-mono₂
    ; identityˡ      to *-identityˡ
    ; identityʳ      to *-identityʳ
    ; isMagma        to *-isMagma
    ; isPromagma     to *-isPromagma
    ; isPomagma      to *-isPomagma
    ; isSemigroup    to *-isSemigroup
    ; isProsemigroup to *-isProsemigroup
    ; isPosemigroup  to *-isPosemigroup
    ; isMonoid       to *-isMonoid
    ; isPromonoid    to *-isPromonoid
    )

  isProsemiring : IsProsemiring + * 0# 1#
  isProsemiring = record
    { +-isCommutativePromonoid = +-isCommutativePromonoid
    ; *-cong                   = *-cong
    ; *-mono                   = *-mono
    ; *-assoc                  = *-assoc
    ; *-identity               = *-identity
    ; distrib                  = distrib
    ; zero                     = zero
    }

  open IsProsemiring isProsemiring public
    using (isSemiring; distribˡ; distribʳ; zeroˡ; zeroʳ)

-- Partially ordered idempotentSemiring (IdempotentPosemiring)

record IsIdempotentPosemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemiring  : IsPosemiring + * 0# 1#
    +-idem      : Idempotent +

  open IsPosemiring isPosemiring public

  isIdempotentProsemiring : IsIdempotentProsemiring + * 0# 1#
  isIdempotentProsemiring = record { isProsemiring = isProsemiring ; +-idem = +-idem }

  open IsIdempotentProsemiring isIdempotentProsemiring public
    using (isIdempotentSemiring; +-idem)

-- Partially ordered KleeneAlgebra (PoKleeneAlgebra)

record IsPoKleeneAlgebra (+ * : Op₂ A) (⋆ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isIdempotentPosemiring  : IsIdempotentPosemiring + * 0# 1#
    starExpansive           : StarExpansive 1# + * ⋆
    starDestructive         : StarDestructive + * ⋆

  open IsIdempotentPosemiring isIdempotentPosemiring public

  isProKleeneAlgebra : IsProKleeneAlgebra + * ⋆ 0# 1#
  isProKleeneAlgebra = record
    { isIdempotentProsemiring = isIdempotentProsemiring
    ; starExpansive           = starExpansive
    ; starDestructive         = starDestructive
    }

  open IsProKleeneAlgebra isProKleeneAlgebra public
    using (isKleeneAlgebra; starExpansive; starDestructive)

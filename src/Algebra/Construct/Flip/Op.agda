------------------------------------------------------------------------
-- The Agda standard library
--
-- Flipping the arguments of a binary operation preserves many of its
-- algebraic properties.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.Flip.Op where

open import Algebra.Core
open import Algebra.Bundles
import Algebra.Definitions as Def
import Algebra.Structures as Str
import Algebra.Consequences.Setoid as Consequences
import Data.Product as Prod
import Data.Sum as Sum
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (Symmetric)

private
  variable
    a ℓ : Level
    A   : Set a
    ≈   : Rel A ℓ
    ε   : A
    ⁻¹  : Op₁ A
    ∙   : Op₂ A

------------------------------------------------------------------------
-- Properties

preserves₂ : (∼ ≈ ≋ : Rel A ℓ) →
             ∙ Preserves₂ ∼ ⟶ ≈ ⟶ ≋ → (flip ∙) Preserves₂ ≈ ⟶ ∼ ⟶ ≋
preserves₂ _ _ _ pres = flip pres

module ∙-Properties (≈ : Rel A ℓ) (∙ : Op₂ A) where

  open Def ≈

  associative : Symmetric ≈ → Associative ∙ → Associative (flip ∙)
  associative sym assoc x y z = sym (assoc z y x)

  identity : Identity ε ∙ → Identity ε (flip ∙)
  identity id = Prod.swap id

  commutative : Commutative ∙ → Commutative (flip ∙)
  commutative comm = flip comm

  selective : Selective ∙ → Selective (flip ∙)
  selective sel x y = Sum.swap (sel y x)

  idempotent : Idempotent ∙ → Idempotent (flip ∙)
  idempotent idem = idem

  inverse : Inverse ε ⁻¹ ∙ → Inverse ε ⁻¹ (flip ∙)
  inverse inv = Prod.swap inv

  zero : Zero ε ∙ → Zero ε (flip ∙)
  zero zer = Prod.swap zer

module *-Properties (≈ : Rel A ℓ) (* + : Op₂ A) where

  open Def ≈

  distributes : * DistributesOver + → (flip *) DistributesOver +
  distributes distrib = Prod.swap distrib

------------------------------------------------------------------------
-- Structures

module _ {≈ : Rel A ℓ} {∙ : Op₂ A} where

  open Def ≈
  open Str ≈
  open ∙-Properties ≈ ∙

  isMagma : IsMagma ∙ → IsMagma (flip ∙)
  isMagma m = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = preserves₂ ≈ ≈ ≈ ∙-cong
    }
    where open IsMagma m

  isSelectiveMagma : IsSelectiveMagma ∙ → IsSelectiveMagma (flip ∙)
  isSelectiveMagma m = record
    { isMagma = isMagma m.isMagma
    ; sel     = selective m.sel
    }
    where module m = IsSelectiveMagma m

  isCommutativeMagma : IsCommutativeMagma ∙ → IsCommutativeMagma (flip ∙)
  isCommutativeMagma m = record
    { isMagma = isMagma m.isMagma
    ; comm    = commutative m.comm
    }
    where module m = IsCommutativeMagma m

  isSemigroup : IsSemigroup ∙ → IsSemigroup (flip ∙)
  isSemigroup s = record
    { isMagma = isMagma s.isMagma
    ; assoc   = associative s.sym s.assoc
    }
    where module s = IsSemigroup s

  isBand : IsBand ∙ → IsBand (flip ∙)
  isBand b = record
    { isSemigroup = isSemigroup b.isSemigroup
    ; idem        = b.idem
    }
    where module b = IsBand b

  isCommutativeSemigroup : IsCommutativeSemigroup ∙ →
                           IsCommutativeSemigroup (flip ∙)
  isCommutativeSemigroup s = record
    { isSemigroup = isSemigroup s.isSemigroup
    ; comm        = commutative s.comm
    }
    where module s = IsCommutativeSemigroup s

  isUnitalMagma : IsUnitalMagma ∙ ε → IsUnitalMagma (flip ∙) ε
  isUnitalMagma m = record
    { isMagma  = isMagma m.isMagma
    ; identity = identity m.identity
    }
    where module m = IsUnitalMagma m

  isMonoid : IsMonoid ∙ ε → IsMonoid (flip ∙) ε
  isMonoid m = record
    { isSemigroup = isSemigroup m.isSemigroup
    ; identity    = identity m.identity
    }
    where module m = IsMonoid m

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε →
                        IsCommutativeMonoid (flip ∙) ε
  isCommutativeMonoid m = record
    { isMonoid = isMonoid m.isMonoid
    ; comm     = commutative m.comm
    }
    where module m = IsCommutativeMonoid m

  isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid ∙ ε →
                                  IsIdempotentCommutativeMonoid (flip ∙) ε
  isIdempotentCommutativeMonoid m = record
    { isCommutativeMonoid = isCommutativeMonoid m.isCommutativeMonoid
    ; idem                = idempotent m.idem
    }
    where module m = IsIdempotentCommutativeMonoid m

  isInvertibleMagma : IsInvertibleMagma ∙ ε ⁻¹ →
                      IsInvertibleMagma (flip ∙) ε ⁻¹
  isInvertibleMagma m = record
    { isMagma = isMagma m.isMagma
    ; inverse = inverse m.inverse
    ; ⁻¹-cong = m.⁻¹-cong
    }
    where module m = IsInvertibleMagma m

  isInvertibleUnitalMagma : IsInvertibleUnitalMagma ∙ ε ⁻¹ →
                            IsInvertibleUnitalMagma (flip ∙) ε ⁻¹
  isInvertibleUnitalMagma m = record
    { isInvertibleMagma = isInvertibleMagma m.isInvertibleMagma
    ; identity          = identity m.identity
    }
    where module m = IsInvertibleUnitalMagma m

  isGroup : IsGroup ∙ ε ⁻¹ → IsGroup (flip ∙) ε ⁻¹
  isGroup g = record
    { isMonoid = isMonoid g.isMonoid
    ; inverse  = inverse g.inverse
    ; ⁻¹-cong  = g.⁻¹-cong
    }
    where module g = IsGroup g

  isAbelianGroup : IsAbelianGroup ∙ ε ⁻¹ → IsAbelianGroup (flip ∙) ε ⁻¹
  isAbelianGroup g = record
    { isGroup = isGroup g.isGroup
    ; comm    = commutative g.comm
    }
    where module g = IsAbelianGroup g

module _ {≈ : Rel A ℓ} {+ * : Op₂ A} {0# 1# : A} where

  open Str ≈
  open ∙-Properties ≈ *
  open *-Properties ≈ * +

  isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero + * 0# 1# →
                                      IsSemiringWithoutAnnihilatingZero + (flip *) 0# 1#
  isSemiringWithoutAnnihilatingZero r = record
    { +-isCommutativeMonoid = r.+-isCommutativeMonoid
    ; *-cong = preserves₂ ≈ ≈ ≈ r.*-cong
    ; *-assoc = associative r.sym r.*-assoc
    ; *-identity = identity r.*-identity
    ; distrib = distributes r.distrib
    }
    where module r = IsSemiringWithoutAnnihilatingZero r

  isSemiring : IsSemiring + * 0# 1# → IsSemiring + (flip *) 0# 1#
  isSemiring r = record
    { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero r.isSemiringWithoutAnnihilatingZero
    ; zero = zero r.zero
    }
    where module r = IsSemiring r

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1# →
                          IsCommutativeSemiring + (flip *) 0# 1#
  isCommutativeSemiring r = record
    { isSemiring = isSemiring r.isSemiring
    ; *-comm = commutative r.*-comm
    }
    where module r = IsCommutativeSemiring r

  isCancellativeCommutativeSemiring : IsCancellativeCommutativeSemiring + * 0# 1# →
                                      IsCancellativeCommutativeSemiring + (flip *) 0# 1#
  isCancellativeCommutativeSemiring r = record
    { isCommutativeSemiring = isCommutativeSemiring r.isCommutativeSemiring
    ; *-cancelˡ-nonZero = Consequences.comm∧almostCancelˡ⇒almostCancelʳ r.setoid r.*-comm r.*-cancelˡ-nonZero
    }
    where module r = IsCancellativeCommutativeSemiring r

  isIdempotentSemiring : IsIdempotentSemiring + * 0# 1# →
                         IsIdempotentSemiring + (flip *) 0# 1#
  isIdempotentSemiring r = record
    { isSemiring = isSemiring r.isSemiring
    ; +-idem = r.+-idem
    }
    where module r = IsIdempotentSemiring r

  isQuasiring : IsQuasiring + * 0# 1# → IsQuasiring + (flip *) 0# 1#
  isQuasiring r = record
    { +-isMonoid = r.+-isMonoid
    ; *-cong = preserves₂ ≈ ≈ ≈ r.*-cong
    ; *-assoc = associative r.sym r.*-assoc
    ; *-identity = identity r.*-identity
    ; distrib = distributes r.distrib
    ; zero = zero r.zero
    }
    where module r = IsQuasiring r

module _ {≈ : Rel A ℓ} {+ * : Op₂ A} { - : Op₁ A} {0# : A} where

  open Str ≈
  open ∙-Properties ≈ *
  open *-Properties ≈ * +

  isRingWithoutOne : IsRingWithoutOne + * - 0# → IsRingWithoutOne + (flip *) - 0#
  isRingWithoutOne r = record
    { +-isAbelianGroup = r.+-isAbelianGroup
    ; *-cong = preserves₂ ≈ ≈ ≈ r.*-cong
    ; *-assoc = associative r.sym r.*-assoc
    ; distrib = distributes r.distrib
    }
    where module r = IsRingWithoutOne r

module _ {≈ : Rel A ℓ} {+ * : Op₂ A} { - : Op₁ A} {0# 1# : A} where

  open Str ≈
  open ∙-Properties ≈ *
  open *-Properties ≈ * +

  isNonAssociativeRing : IsNonAssociativeRing + * - 0# 1# →
                         IsNonAssociativeRing + (flip *) - 0# 1#
  isNonAssociativeRing r = record
    { +-isAbelianGroup = r.+-isAbelianGroup
    ; *-cong = preserves₂ ≈ ≈ ≈ r.*-cong
    ; *-identity = identity r.*-identity
    ; distrib = distributes r.distrib
    ; zero = zero r.zero
    }
    where module r = IsNonAssociativeRing r

  isNearring : IsNearring + * 0# 1# - → IsNearring + (flip *) 0# 1# -
  isNearring r = record
    { isQuasiring = isQuasiring r.isQuasiring
    ; +-inverse = r.+-inverse
    ; ⁻¹-cong = r.⁻¹-cong
    }
    where module r = IsNearring r

  isRing : IsRing + * - 0# 1# → IsRing + (flip *) - 0# 1#
  isRing r = record
    { +-isAbelianGroup = r.+-isAbelianGroup
    ; *-cong = preserves₂ ≈ ≈ ≈ r.*-cong
    ; *-assoc = associative r.sym r.*-assoc
    ; *-identity = identity r.*-identity
    ; distrib = distributes r.distrib
    }
    where module r = IsRing r

  isCommutativeRing : IsCommutativeRing + * - 0# 1# →
                      IsCommutativeRing + (flip *) - 0# 1#
  isCommutativeRing r = record
    { isRing = isRing r.isRing
    ; *-comm = commutative r.*-comm
    }
    where module r = IsCommutativeRing r


------------------------------------------------------------------------
-- Bundles

magma : Magma a ℓ → Magma a ℓ
magma m = record { isMagma = isMagma m.isMagma }
  where module m = Magma m

commutativeMagma : CommutativeMagma a ℓ → CommutativeMagma a ℓ
commutativeMagma m = record
  { isCommutativeMagma = isCommutativeMagma m.isCommutativeMagma
  }
  where module m = CommutativeMagma m

selectiveMagma : SelectiveMagma a ℓ → SelectiveMagma a ℓ
selectiveMagma m = record
  { isSelectiveMagma = isSelectiveMagma m.isSelectiveMagma
  }
  where module m = SelectiveMagma m

semigroup : Semigroup a ℓ → Semigroup a ℓ
semigroup s = record { isSemigroup = isSemigroup s.isSemigroup }
  where module s = Semigroup s

band : Band a ℓ → Band a ℓ
band b = record { isBand = isBand b.isBand }
  where module b = Band b

commutativeSemigroup : CommutativeSemigroup a ℓ → CommutativeSemigroup a ℓ
commutativeSemigroup s = record
  { isCommutativeSemigroup = isCommutativeSemigroup s.isCommutativeSemigroup
  }
  where module s = CommutativeSemigroup s

unitalMagma : UnitalMagma a ℓ → UnitalMagma a ℓ
unitalMagma m = record
  { isUnitalMagma = isUnitalMagma m.isUnitalMagma
  }
  where module m = UnitalMagma m

monoid : Monoid a ℓ → Monoid a ℓ
monoid m = record { isMonoid = isMonoid m.isMonoid }
  where module m = Monoid m

commutativeMonoid : CommutativeMonoid a ℓ → CommutativeMonoid a ℓ
commutativeMonoid m = record
  { isCommutativeMonoid = isCommutativeMonoid m.isCommutativeMonoid
  }
  where module m = CommutativeMonoid m

idempotentCommutativeMonoid : IdempotentCommutativeMonoid a ℓ →
                              IdempotentCommutativeMonoid a ℓ
idempotentCommutativeMonoid m = record
  { isIdempotentCommutativeMonoid =
      isIdempotentCommutativeMonoid m.isIdempotentCommutativeMonoid
  }
  where module m = IdempotentCommutativeMonoid m

invertibleMagma : InvertibleMagma a ℓ → InvertibleMagma a ℓ
invertibleMagma m = record
  { isInvertibleMagma = isInvertibleMagma m.isInvertibleMagma
  }
  where module m = InvertibleMagma m

invertibleUnitalMagma : InvertibleUnitalMagma a ℓ → InvertibleUnitalMagma a ℓ
invertibleUnitalMagma m = record
  { isInvertibleUnitalMagma = isInvertibleUnitalMagma m.isInvertibleUnitalMagma
  }
  where module m = InvertibleUnitalMagma m

group : Group a ℓ → Group a ℓ
group g = record { isGroup = isGroup g.isGroup }
  where module g = Group g

abelianGroup : AbelianGroup a ℓ → AbelianGroup a ℓ
abelianGroup g = record { isAbelianGroup = isAbelianGroup g.isAbelianGroup }
  where module g = AbelianGroup g

semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ →
                                  SemiringWithoutAnnihilatingZero a ℓ
semiringWithoutAnnihilatingZero r = record
  { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero r.isSemiringWithoutAnnihilatingZero }
  where module r = SemiringWithoutAnnihilatingZero r

semiring : Semiring a ℓ → Semiring a ℓ
semiring r = record { isSemiring = isSemiring r.isSemiring }
  where module r = Semiring r

commutativeSemiring : CommutativeSemiring a ℓ → CommutativeSemiring a ℓ
commutativeSemiring r = record
  { isCommutativeSemiring = isCommutativeSemiring r.isCommutativeSemiring }
  where module r = CommutativeSemiring r

cancellativeCommutativeSemiring : CancellativeCommutativeSemiring a ℓ →
                                  CancellativeCommutativeSemiring a ℓ
cancellativeCommutativeSemiring r = record
  { isCancellativeCommutativeSemiring = isCancellativeCommutativeSemiring r.isCancellativeCommutativeSemiring }
  where module r = CancellativeCommutativeSemiring r

idempotentSemiring : IdempotentSemiring a ℓ → IdempotentSemiring a ℓ
idempotentSemiring r = record
  { isIdempotentSemiring = isIdempotentSemiring r.isIdempotentSemiring }
  where module r = IdempotentSemiring r

quasiring : Quasiring a ℓ → Quasiring a ℓ
quasiring r = record { isQuasiring = isQuasiring r.isQuasiring }
  where module r = Quasiring r

ringWithoutOne : RingWithoutOne a ℓ → RingWithoutOne a ℓ
ringWithoutOne r = record { isRingWithoutOne = isRingWithoutOne r.isRingWithoutOne }
  where module r = RingWithoutOne r

nonAssociativeRing : NonAssociativeRing a ℓ → NonAssociativeRing a ℓ
nonAssociativeRing r = record
  { isNonAssociativeRing = isNonAssociativeRing r.isNonAssociativeRing }
  where module r = NonAssociativeRing r

nearring : Nearring a ℓ → Nearring a ℓ
nearring r = record { isNearring = isNearring r.isNearring }
  where module r = Nearring r

ring : Ring a ℓ → Ring a ℓ
ring r = record { isRing = isRing r.isRing }
  where module r = Ring r

commutativeRing : CommutativeRing a ℓ → CommutativeRing a ℓ
commutativeRing r = record { isCommutativeRing = isCommutativeRing r.isCommutativeRing }
  where module r = CommutativeRing r

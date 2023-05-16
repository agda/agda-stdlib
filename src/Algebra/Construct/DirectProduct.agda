------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures made by taking two other instances
-- A and B, and having elements of the new instance be pairs |A| × |B|.
-- In mathematics, this would usually be written A × B or A ⊕ B.
--
-- From semigroups up, these new instances are products of the relevant
-- category. For structures with commutative addition (commutative
-- monoids, Abelian groups, semirings, rings), the direct product is
-- also the coproduct, making it a biproduct.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.DirectProduct where

open import Algebra
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Raw bundles

rawMagma : RawMagma a ℓ₁ → RawMagma b ℓ₂ → RawMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawMagma M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  } where module M = RawMagma M; module N = RawMagma N

rawMonoid : RawMonoid a ℓ₁ → RawMonoid b ℓ₂ → RawMonoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawMonoid M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; ε       = M.ε , N.ε
  } where module M = RawMonoid M; module N = RawMonoid N

rawGroup : RawGroup a ℓ₁ → RawGroup b ℓ₂ → RawGroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawGroup G H = record
  { Carrier = G.Carrier × H.Carrier
  ; _≈_     = Pointwise G._≈_ H._≈_
  ; _∙_     = zip G._∙_ H._∙_
  ; ε       = G.ε , H.ε
  ; _⁻¹     = map G._⁻¹ H._⁻¹
  } where module G = RawGroup G; module H = RawGroup H

rawSemiring : RawSemiring a ℓ₁ → RawSemiring b ℓ₂ → RawSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawSemiring R S = record
  { Carrier = R.Carrier × S.Carrier
  ; _≈_     = Pointwise R._≈_ S._≈_
  ; _+_     = zip R._+_ S._+_
  ; _*_     = zip R._*_ S._*_
  ; 0#      = R.0# , S.0#
  ; 1#      = R.1# , S.1#
  } where module R = RawSemiring R; module S = RawSemiring S

rawRing : RawRing a ℓ₁ → RawRing b ℓ₂ → RawRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawRing R S = record
  { Carrier = R.Carrier × S.Carrier
  ; _≈_     = Pointwise R._≈_ S._≈_
  ; _+_     = zip R._+_ S._+_
  ; _*_     = zip R._*_ S._*_
  ; -_      = map R.-_ S.-_
  ; 0#      = R.0# , S.0#
  ; 1#      = R.1# , S.1#
  } where module R = RawRing R; module S = RawRing S

rawQuasigroup : RawQuasigroup a ℓ₁ → RawQuasigroup b ℓ₂ → RawQuasigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawQuasigroup M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; _\\_    = zip M._\\_ N._\\_
  ; _//_    = zip M._//_ N._//_
  } where module M = RawQuasigroup M; module N = RawQuasigroup N

rawLoop : RawLoop a ℓ₁ → RawLoop b ℓ₂ → RawLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawLoop M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; _\\_    = zip M._\\_ N._\\_
  ; _//_    = zip M._//_ N._//_
  ; ε       = M.ε , N.ε
  } where module M = RawLoop M; module N = RawLoop N

------------------------------------------------------------------------
-- Bundles

magma : Magma a ℓ₁ → Magma b ℓ₂ → Magma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
magma M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; isMagma = record
    { isEquivalence = ×-isEquivalence M.isEquivalence N.isEquivalence
    ; ∙-cong = zip M.∙-cong N.∙-cong
    }
  } where module M = Magma M; module N = Magma N

idempotentMagma : IdempotentMagma a ℓ₁ → IdempotentMagma b ℓ₂ → IdempotentMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
idempotentMagma G H = record
  { isIdempotentMagma = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; idem = λ x → (G.idem , H.idem) <*> x
    }
  } where module G = IdempotentMagma G; module H = IdempotentMagma H

alternativeMagma : AlternativeMagma a ℓ₁ → AlternativeMagma b ℓ₂ → AlternativeMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
alternativeMagma G H = record
  { isAlternativeMagma = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; alter = (λ x y → G.alternativeˡ , H.alternativeˡ <*> x <*> y)
            , (λ x y → G.alternativeʳ , H.alternativeʳ <*> x <*> y)
    }
  } where module G = AlternativeMagma G; module H = AlternativeMagma H

flexibleMagma : FlexibleMagma a ℓ₁ → FlexibleMagma b ℓ₂ → FlexibleMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
flexibleMagma G H = record
  { isFlexibleMagma = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; flex = λ x y → (G.flex , H.flex) <*> x <*> y
    }
  } where module G = FlexibleMagma G; module H = FlexibleMagma H

medialMagma : MedialMagma a ℓ₁ → MedialMagma b ℓ₂ → MedialMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
medialMagma G H = record
  { isMedialMagma = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; medial = λ x y u z → (G.medial , H.medial) <*> x <*> y <*> u <*> z
    }
  } where module G = MedialMagma G; module H = MedialMagma H

semimedialMagma : SemimedialMagma a ℓ₁ → SemimedialMagma b ℓ₂ → SemimedialMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semimedialMagma G H = record
  { isSemimedialMagma = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; semiMedial = (λ x y z → G.semimedialˡ , H.semimedialˡ <*> x <*> y <*> z)
                 , ((λ x y z → G.semimedialʳ , H.semimedialʳ <*> x <*> y <*> z))
    }
  } where module G = SemimedialMagma G; module H = SemimedialMagma H

semigroup : Semigroup a ℓ₁ → Semigroup b ℓ₂ → Semigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semigroup G H = record
  { isSemigroup = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; assoc = λ x y z → (G.assoc , H.assoc) <*> x <*> y <*> z
    }
  } where module G = Semigroup G; module H = Semigroup H

band : Band a ℓ₁ → Band b ℓ₂ → Band (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
band B C = record
  { isBand = record
    { isSemigroup = Semigroup.isSemigroup (semigroup B.semigroup C.semigroup)
    ; idem = λ x → (B.idem , C.idem) <*> x
    }
  } where module B = Band B; module C = Band C

commutativeSemigroup : CommutativeSemigroup a ℓ₁ → CommutativeSemigroup b ℓ₂ →
                       CommutativeSemigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
commutativeSemigroup G H = record
  { isCommutativeSemigroup = record
    { isSemigroup = Semigroup.isSemigroup (semigroup G.semigroup H.semigroup)
    ; comm = λ x y → (G.comm , H.comm) <*> x <*> y
    }
  } where module G = CommutativeSemigroup G; module H = CommutativeSemigroup H

unitalMagma : UnitalMagma a ℓ₁ → UnitalMagma b ℓ₂ → UnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
unitalMagma M N = record
  { ε = M.ε , N.ε
  ; isUnitalMagma = record
    { isMagma = Magma.isMagma (magma M.magma N.magma)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = UnitalMagma M; module N = UnitalMagma N

monoid : Monoid a ℓ₁ → Monoid b ℓ₂ → Monoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
monoid M N = record
  { ε = M.ε , N.ε
  ; isMonoid = record
    { isSemigroup = Semigroup.isSemigroup (semigroup M.semigroup N.semigroup)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = Monoid M; module N = Monoid N

commutativeMonoid : CommutativeMonoid a ℓ₁ → CommutativeMonoid b ℓ₂ →
                    CommutativeMonoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
commutativeMonoid M N = record
  { isCommutativeMonoid = record
    { isMonoid = Monoid.isMonoid (monoid M.monoid N.monoid)
    ; comm = λ x y → (M.comm , N.comm) <*> x <*> y
    }
  } where module M = CommutativeMonoid M; module N = CommutativeMonoid N

idempotentCommutativeMonoid :
  IdempotentCommutativeMonoid a ℓ₁ → IdempotentCommutativeMonoid b ℓ₂ →
  IdempotentCommutativeMonoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
idempotentCommutativeMonoid M N = record
  { isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
      (commutativeMonoid M.commutativeMonoid N.commutativeMonoid)
    ; idem = λ x → (M.idem , N.idem) <*> x
    }
  }
  where
  module M = IdempotentCommutativeMonoid M
  module N = IdempotentCommutativeMonoid N

invertibleMagma : InvertibleMagma a ℓ₁ → InvertibleMagma b ℓ₂ → InvertibleMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
invertibleMagma M N = record
  { _⁻¹ = map M._⁻¹ N._⁻¹
  ; isInvertibleMagma = record
    { isMagma = Magma.isMagma (magma M.magma N.magma)
    ; inverse = (λ x → (M.inverseˡ , N.inverseˡ) <*> x)
                , (λ x → (M.inverseʳ , N.inverseʳ) <*> x)
    ; ⁻¹-cong = map M.⁻¹-cong N.⁻¹-cong
    }
  } where module M = InvertibleMagma M; module N = InvertibleMagma N

invertibleUnitalMagma : InvertibleUnitalMagma a ℓ₁ → InvertibleUnitalMagma b ℓ₂ → InvertibleUnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
invertibleUnitalMagma M N = record
  { ε = M.ε , N.ε
  ; isInvertibleUnitalMagma = record
    { isInvertibleMagma = InvertibleMagma.isInvertibleMagma (invertibleMagma M.invertibleMagma N.invertibleMagma)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = InvertibleUnitalMagma M; module N = InvertibleUnitalMagma N

group : Group a ℓ₁ → Group b ℓ₂ → Group (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
group G H = record
  { _⁻¹ = map G._⁻¹ H._⁻¹
  ; isGroup = record
    { isMonoid = Monoid.isMonoid (monoid G.monoid H.monoid)
    ; inverse = (λ x → (G.inverseˡ , H.inverseˡ) <*> x)
              , (λ x → (G.inverseʳ , H.inverseʳ) <*> x)
    ; ⁻¹-cong = map G.⁻¹-cong H.⁻¹-cong
    }
  } where module G = Group G; module H = Group H

abelianGroup : AbelianGroup a ℓ₁ → AbelianGroup b ℓ₂ →
               AbelianGroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
abelianGroup G H = record
  { isAbelianGroup = record
    { isGroup = Group.isGroup (group G.group H.group)
    ; comm = λ x y → (G.comm , H.comm) <*> x <*> y
    }
  } where module G = AbelianGroup G; module H = AbelianGroup H

semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ₁ →
                                  SemiringWithoutAnnihilatingZero b ℓ₂ →
                                  SemiringWithoutAnnihilatingZero (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semiringWithoutAnnihilatingZero R S = record
  { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
                                  (commutativeMonoid R.+-commutativeMonoid
                                                     S.+-commutativeMonoid)
      ; *-cong = zip R.*-cong S.*-cong
      ; *-assoc = λ x y z → (R.*-assoc , S.*-assoc) <*> x <*> y <*> z
      ; *-identity = (R.*-identityˡ , S.*-identityˡ <*>_)
                   , (R.*-identityʳ , S.*-identityʳ <*>_)
      ; distrib    = (λ x y z → (R.distribˡ , S.distribˡ) <*> x <*> y <*> z)
                   , (λ x y z → (R.distribʳ , S.distribʳ) <*> x <*> y <*> z)
      }
  } where module R = SemiringWithoutAnnihilatingZero R
          module S = SemiringWithoutAnnihilatingZero S

semiring : Semiring a ℓ₁ → Semiring b ℓ₂ → Semiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semiring R S = record
  { isSemiring = record
      { isSemiringWithoutAnnihilatingZero =
          SemiringWithoutAnnihilatingZero.isSemiringWithoutAnnihilatingZero U
      ; zero = uncurry (λ x y → R.zeroˡ x , S.zeroˡ y)
             , uncurry (λ x y → R.zeroʳ x , S.zeroʳ y)
      }
  }
  where
  module R = Semiring R
  module S = Semiring S
  U = semiringWithoutAnnihilatingZero R.semiringWithoutAnnihilatingZero
                                      S.semiringWithoutAnnihilatingZero

commutativeSemiring : CommutativeSemiring a ℓ₁ → CommutativeSemiring b ℓ₂ →
                      CommutativeSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
commutativeSemiring R S = record
  { isCommutativeSemiring = record
      { isSemiring = Semiring.isSemiring (semiring R.semiring S.semiring)
      ; *-comm     = λ x y → (R.*-comm , S.*-comm) <*> x <*> y
      }
  } where module R = CommutativeSemiring R;  module S = CommutativeSemiring S

idempotentSemiring : IdempotentSemiring a ℓ₁ → IdempotentSemiring b ℓ₂ → IdempotentSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
idempotentSemiring K L = record
  { isIdempotentSemiring = record
      { isSemiring = Semiring.isSemiring (semiring K.semiring L.semiring)
      ; +-idem = λ x → (K.+-idem , L.+-idem) <*> x
      }
  } where module K = IdempotentSemiring K;  module L = IdempotentSemiring L

kleeneAlgebra : KleeneAlgebra a ℓ₁ → KleeneAlgebra b ℓ₂ → KleeneAlgebra (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
kleeneAlgebra K L = record
  { isKleeneAlgebra = record
      { isIdempotentSemiring = IdempotentSemiring.isIdempotentSemiring (idempotentSemiring K.idempotentSemiring L.idempotentSemiring)
      ; starExpansive = (λ x → (K.starExpansiveˡ  , L.starExpansiveˡ) <*> x)
                      , (λ x → (K.starExpansiveʳ  , L.starExpansiveʳ) <*> x)
      ; starDestructive = (λ a b x x₁ → (K.starDestructiveˡ  , L.starDestructiveˡ) <*> a <*> b <*> x <*> x₁)
                        , (λ a b x x₁ → (K.starDestructiveʳ  , L.starDestructiveʳ) <*> a <*> b <*> x <*> x₁)
      }
  } where module K = KleeneAlgebra K;  module L = KleeneAlgebra L

ring : Ring a ℓ₁ → Ring b ℓ₂ → Ring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
ring R S = record
  { -_     = uncurry (λ x y → R.-_ x , S.-_ y)
  ; isRing = record
      { +-isAbelianGroup = AbelianGroup.isAbelianGroup A
      ; *-cong           = Semiring.*-cong Semi
      ; *-assoc          = Semiring.*-assoc Semi
      ; *-identity       = Semiring.*-identity Semi
      ; distrib          = Semiring.distrib Semi
      ; zero             = Semiring.zero Semi
      }
  }
  where
  module R = Ring R
  module S = Ring S
  Semi = semiring R.semiring S.semiring
  A    = abelianGroup R.+-abelianGroup S.+-abelianGroup

commutativeRing : CommutativeRing a ℓ₁ → CommutativeRing b ℓ₂ →
                  CommutativeRing (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
commutativeRing R S = record
  { isCommutativeRing = record
      { isRing = Ring.isRing (ring R.ring S.ring)
      ; *-comm = λ x y → (R.*-comm , S.*-comm) <*> x <*> y
      }
  } where module R = CommutativeRing R; module S = CommutativeRing S

quasigroup : Quasigroup a ℓ₁ → Quasigroup b ℓ₂ → Quasigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
quasigroup M N = record
  { _\\_    = zip M._\\_ N._\\_
  ; _//_    = zip M._//_ N._//_
  ; isQuasigroup = record
    { isMagma = Magma.isMagma (magma M.magma N.magma)
    ; \\-cong = zip M.\\-cong N.\\-cong
    ; //-cong = zip M.//-cong N.//-cong
    ; leftDivides = (λ x y → M.leftDividesˡ , N.leftDividesˡ <*> x <*> y) , (λ x y → M.leftDividesʳ , N.leftDividesʳ <*> x <*> y)
    ; rightDivides = (λ x y → M.rightDividesˡ , N.rightDividesˡ <*> x <*> y) , (λ x y → M.rightDividesʳ , N.rightDividesʳ <*> x <*> y)
    }
  } where module M = Quasigroup M; module N = Quasigroup N

loop : Loop a ℓ₁ → Loop b ℓ₂ → Loop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
loop M N = record
  { ε = M.ε , N.ε
  ; isLoop = record
    { isQuasigroup = Quasigroup.isQuasigroup (quasigroup M.quasigroup N.quasigroup)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = Loop M; module N = Loop N

leftBolLoop : LeftBolLoop a ℓ₁ → LeftBolLoop b ℓ₂ → LeftBolLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
leftBolLoop M N = record
  { isLeftBolLoop = record
    { isLoop = Loop.isLoop (loop M.loop N.loop)
    ; leftBol = λ x y z → M.leftBol , N.leftBol <*> x <*> y <*> z
    }
  } where module M = LeftBolLoop M; module N = LeftBolLoop N

rightBolLoop : RightBolLoop a ℓ₁ → RightBolLoop b ℓ₂ → RightBolLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rightBolLoop M N = record
  { isRightBolLoop = record
    { isLoop = Loop.isLoop (loop M.loop N.loop)
    ; rightBol = λ x y z → M.rightBol , N.rightBol <*> x <*> y <*> z
    }
  } where module M = RightBolLoop M; module N = RightBolLoop N

middleBolLoop : MiddleBolLoop a ℓ₁ → MiddleBolLoop b ℓ₂ → MiddleBolLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
middleBolLoop M N = record
  { isMiddleBolLoop = record
    { isLoop = Loop.isLoop (loop M.loop N.loop)
    ; middleBol = λ x y z → M.middleBol , N.middleBol <*> x <*> y <*> z
    }
  } where module M = MiddleBolLoop M; module N = MiddleBolLoop N

moufangLoop : MoufangLoop a ℓ₁ → MoufangLoop b ℓ₂ → MoufangLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
moufangLoop M N = record
  { isMoufangLoop = record
    { isLeftBolLoop = LeftBolLoop.isLeftBolLoop (leftBolLoop M.leftBolLoop N.leftBolLoop)
    ; rightBol = λ x y z → M.rightBol , N.rightBol <*> x <*> y <*> z
    ; identical = λ x y z → M.identical , N.identical <*> x <*> y <*> z
    }
  } where module M = MoufangLoop M; module N = MoufangLoop N

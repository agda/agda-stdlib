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

{-# OPTIONS --without-K --safe #-}

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

semilattice : Semilattice a ℓ₁ → Semilattice b ℓ₂ →
              Semilattice (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
semilattice L M = record
  { isSemilattice = record
    { isBand = Band.isBand (band L.band M.band)
    ; comm = λ x y → (L.comm , M.comm) <*> x <*> y
    }
  } where module L = Semilattice L; module M = Semilattice M

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

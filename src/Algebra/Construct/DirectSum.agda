------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of algebraic structures made by taking two other instances
-- A and B, and having elements of the new instance be pairs |A| × |B|.
-- In mathematics, this would usually be written A ⊕ B.
--
-- From monoids up, these new instances are biproducts – i.e, both
-- products and coproducts of the relevant category.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Construct.DirectSum where

open import Algebra
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level using (Level; _⊔_)

private
  variable
    c cℓ d dℓ : Level

rawMagma : RawMagma c cℓ → RawMagma d dℓ → RawMagma (c ⊔ d) (cℓ ⊔ dℓ)
rawMagma M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_ = Pointwise M._≈_ N._≈_
  ; _∙_ = zip M._∙_ N._∙_
  }
  where
  module M = RawMagma M
  module N = RawMagma N

magma : Magma c cℓ → Magma d dℓ → Magma (c ⊔ d) (cℓ ⊔ dℓ)
magma M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_ = Pointwise M._≈_ N._≈_
  ; _∙_ = zip M._∙_ N._∙_
  ; isMagma = record
    { isEquivalence = ×-isEquivalence M.isEquivalence N.isEquivalence
    ; ∙-cong = zip M.∙-cong N.∙-cong
    }
  }
  where
  module M = Magma M
  module N = Magma N

semigroup : Semigroup c cℓ → Semigroup d dℓ → Semigroup (c ⊔ d) (cℓ ⊔ dℓ)
semigroup G H = record
  { isSemigroup = record
    { isMagma = Magma.isMagma (magma G.magma H.magma)
    ; assoc = λ x y z → (G.assoc , H.assoc) <*> x <*> y <*> z
    }
  }
  where
  module G = Semigroup G
  module H = Semigroup H

band : Band c cℓ → Band d dℓ → Band (c ⊔ d) (cℓ ⊔ dℓ)
band B C = record
  { isBand = record
    { isSemigroup = Semigroup.isSemigroup (semigroup B.semigroup C.semigroup)
    ; idem = λ x → (B.idem , C.idem) <*> x
    }
  }
  where
  module B = Band B
  module C = Band C

commutativeSemigroup : CommutativeSemigroup c cℓ → CommutativeSemigroup d dℓ →
                       CommutativeSemigroup (c ⊔ d) (cℓ ⊔ dℓ)
commutativeSemigroup G H = record
  { isCommutativeSemigroup = record
    { isSemigroup = Semigroup.isSemigroup (semigroup G.semigroup H.semigroup)
    ; comm = λ x y → (G.comm , H.comm) <*> x <*> y
    }
  }
  where
  module G = CommutativeSemigroup G
  module H = CommutativeSemigroup H

semilattice : Semilattice c cℓ → Semilattice d dℓ →
              Semilattice (c ⊔ d) (cℓ ⊔ dℓ)
semilattice L M = record
  { isSemilattice = record
    { isBand = Band.isBand (band L.band M.band)
    ; comm = λ x y → (L.comm , M.comm) <*> x <*> y
    }
  }
  where
  module L = Semilattice L
  module M = Semilattice M

rawMonoid : RawMonoid c cℓ → RawMonoid d dℓ → RawMonoid (c ⊔ d) (cℓ ⊔ dℓ)
rawMonoid M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_ = Pointwise M._≈_ N._≈_
  ; _∙_ = zip M._∙_ N._∙_
  ; ε = M.ε , N.ε
  }
  where
  module M = RawMonoid M
  module N = RawMonoid N

monoid : Monoid c cℓ → Monoid d dℓ → Monoid (c ⊔ d) (cℓ ⊔ dℓ)
monoid M N = record
  { ε = M.ε , N.ε
  ; isMonoid = record
    { isSemigroup = Semigroup.isSemigroup (semigroup M.semigroup N.semigroup)
    ; identity = (λ x → (M.identityˡ , N.identityˡ) <*> x)
               , (λ x → (M.identityʳ , N.identityʳ) <*> x)
    }
  }
  where
  module M = Monoid M
  module N = Monoid N

commutativeMonoid : CommutativeMonoid c cℓ → CommutativeMonoid d dℓ →
                    CommutativeMonoid (c ⊔ d) (cℓ ⊔ dℓ)
commutativeMonoid M N = record
  { isCommutativeMonoid = record
    { isMonoid = Monoid.isMonoid (monoid M.monoid N.monoid)
    ; comm = λ x y → (M.comm , N.comm) <*> x <*> y
    }
  }
  where
  module M = CommutativeMonoid M
  module N = CommutativeMonoid N

idempotentCommutativeMonoid :
  IdempotentCommutativeMonoid c cℓ → IdempotentCommutativeMonoid d dℓ →
  IdempotentCommutativeMonoid (c ⊔ d) (cℓ ⊔ dℓ)
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

rawGroup : RawGroup c cℓ → RawGroup d dℓ → RawGroup (c ⊔ d) (cℓ ⊔ dℓ)
rawGroup G H = record
  { Carrier = G.Carrier × H.Carrier
  ; _≈_ = Pointwise G._≈_ H._≈_
  ; _∙_ = zip G._∙_ H._∙_
  ; ε = G.ε , H.ε
  ; _⁻¹ = map G._⁻¹ H._⁻¹
  }
  where
  module G = RawGroup G
  module H = RawGroup H

group : Group c cℓ → Group d dℓ → Group (c ⊔ d) (cℓ ⊔ dℓ)
group G H = record
  { _⁻¹ = map G._⁻¹ H._⁻¹
  ; isGroup = record
    { isMonoid = Monoid.isMonoid (monoid G.monoid H.monoid)
    ; inverse = (λ x → (G.inverseˡ , H.inverseˡ) <*> x)
              , (λ x → (G.inverseʳ , H.inverseʳ) <*> x)
    ; ⁻¹-cong = map G.⁻¹-cong H.⁻¹-cong
    }
  }
  where
  module G = Group G
  module H = Group H

abelianGroup : AbelianGroup c cℓ → AbelianGroup d dℓ →
               AbelianGroup (c ⊔ d) (cℓ ⊔ dℓ)
abelianGroup G H = record
  { isAbelianGroup = record
    { isGroup = Group.isGroup (group G.group H.group)
    ; comm = λ x y → (G.comm , H.comm) <*> x <*> y
    }
  }
  where
  module G = AbelianGroup G
  module H = AbelianGroup H

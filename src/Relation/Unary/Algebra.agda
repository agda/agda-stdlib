------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of constructions over unary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Algebra where

open import Algebra.Bundles
import Algebra.Definitions as AlgebraicDefinitions
open import Algebra.Lattice.Bundles
import Algebra.Lattice.Structures as AlgebraicLatticeStructures
import Algebra.Structures as AlgebraicStructures
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product as Product using (_,_; proj₁; proj₂; <_,_>; curry; uncurry)
open import Data.Sum as Sum using (inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (tt)
open import Function.Base using (id; const; _∘_)
open import Level
open import Relation.Unary hiding (∅; U)
open import Relation.Unary.Polymorphic using (∅; U)
open import Relation.Unary.Relation.Binary.Equality using (≐-isEquivalence)

module _ {a ℓ : Level} {A : Set a} where

  open AlgebraicDefinitions {A = Pred A ℓ} _≐_

------------------------------------------------------------------------
-- Properties of _∩_

  ∩-cong : Congruent₂ _∩_
  ∩-cong (P⊆Q , Q⊆P) (R⊆S , S⊆R) = Product.map P⊆Q R⊆S , Product.map Q⊆P S⊆R

  ∩-comm : Commutative _∩_
  ∩-comm _ _ = Product.swap , Product.swap

  ∩-assoc : Associative _∩_
  ∩-assoc _ _ _ = Product.assocʳ′ , Product.assocˡ′

  ∩-idem : Idempotent _∩_
  ∩-idem _ = proj₁ , < id , id >

  ∩-identityˡ : LeftIdentity U _∩_
  ∩-identityˡ _ = proj₂ , < const tt , id >

  ∩-identityʳ : RightIdentity U _∩_
  ∩-identityʳ _ = proj₁ , < id , const tt >

  ∩-identity : Identity U _∩_
  ∩-identity = ∩-identityˡ , ∩-identityʳ

  ∩-zeroˡ : LeftZero ∅ _∩_
  ∩-zeroˡ _ = proj₁ , ⊥-elim

  ∩-zeroʳ : RightZero ∅ _∩_
  ∩-zeroʳ _ = proj₂ , ⊥-elim

  ∩-zero : Zero ∅ _∩_
  ∩-zero = ∩-zeroˡ , ∩-zeroʳ

------------------------------------------------------------------------
-- Properties of _∪_

  ∪-cong : Congruent₂ _∪_
  ∪-cong (P⊆Q , Q⊆P) (R⊆S , S⊆R) = Sum.map P⊆Q R⊆S , Sum.map Q⊆P S⊆R

  ∪-comm : Commutative _∪_
  ∪-comm _ _ = Sum.swap , Sum.swap

  ∪-assoc : Associative _∪_
  ∪-assoc _ _ _ = Sum.assocʳ , Sum.assocˡ

  ∪-idem : Idempotent _∪_
  ∪-idem _ = [ id , id ] , inj₁

  ∪-identityˡ : LeftIdentity ∅ _∪_
  ∪-identityˡ _ = [ ⊥-elim , id ] , inj₂

  ∪-identityʳ : RightIdentity ∅ _∪_
  ∪-identityʳ _ = [ id , ⊥-elim ] , inj₁

  ∪-identity : Identity ∅ _∪_
  ∪-identity = ∪-identityˡ , ∪-identityʳ

------------------------------------------------------------------------
-- Properties of _∩_ and _∪_

  ∩-distribˡ-∪ : _∩_ DistributesOverˡ _∪_
  ∩-distribˡ-∪ _ _ _ =
    ( uncurry (λ x∈P → [ inj₁ ∘ (x∈P ,_) , inj₂ ∘ (x∈P ,_) ])
    , [ Product.map₂ inj₁ , Product.map₂ inj₂ ]
    )

  ∩-distribʳ-∪ : _∩_ DistributesOverʳ _∪_
  ∩-distribʳ-∪ _ _ _ =
    ( uncurry [ curry inj₁ , curry inj₂ ]
    , [ Product.map₁ inj₁ , Product.map₁ inj₂ ]
    )

  ∩-distrib-∪ : _∩_ DistributesOver _∪_
  ∩-distrib-∪ = ∩-distribˡ-∪ , ∩-distribʳ-∪

  ∪-distribˡ-∩ : _∪_ DistributesOverˡ _∩_
  ∪-distribˡ-∩ _ _ _ =
    ( [ < inj₁ , inj₁ > , Product.map inj₂ inj₂ ]
    , uncurry [ const ∘ inj₁ , (λ x∈Q → [ inj₁ , inj₂ ∘ (x∈Q ,_) ]) ]
    )

  ∪-distribʳ-∩ : _∪_ DistributesOverʳ _∩_
  ∪-distribʳ-∩ _ _ _ =
    ( [ Product.map inj₁ inj₁ , < inj₂ , inj₂ > ]
    , uncurry [ (λ x∈Q → [ inj₁ ∘ (x∈Q ,_) , inj₂ ]) , const ∘ inj₂ ]
    )

  ∪-distrib-∩ : _∪_ DistributesOver _∩_
  ∪-distrib-∩ = ∪-distribˡ-∩ , ∪-distribʳ-∩

  ∩-abs-∪ : _∩_ Absorbs _∪_
  ∩-abs-∪ _ _ = proj₁ , < id , inj₁ >

  ∪-abs-∩ : _∪_ Absorbs _∩_
  ∪-abs-∩ _ _ = [ id , proj₁ ] , inj₁

  ∪-∩-absorptive : Absorptive _∪_ _∩_
  ∪-∩-absorptive = ∪-abs-∩ , ∩-abs-∪

  ∩-∪-absorptive : Absorptive _∩_ _∪_
  ∩-∪-absorptive = ∩-abs-∪ , ∪-abs-∩

module _ {a : Level} (A : Set a) (ℓ : Level) where

  open AlgebraicStructures        {A = Pred A ℓ} _≐_
  open AlgebraicLatticeStructures {A = Pred A ℓ} _≐_

------------------------------------------------------------------------
-- Algebraic structures of _∩_

  ∩-isMagma : IsMagma _∩_
  ∩-isMagma = record
    { isEquivalence = ≐-isEquivalence
    ; ∙-cong = ∩-cong
    }

  ∩-isSemigroup : IsSemigroup _∩_
  ∩-isSemigroup = record
    { isMagma = ∩-isMagma
    ; assoc = ∩-assoc
    }

  ∩-isBand : IsBand _∩_
  ∩-isBand = record
    { isSemigroup = ∩-isSemigroup
    ; idem = ∩-idem
    }

  ∩-isSemilattice : IsSemilattice _∩_
  ∩-isSemilattice = record
    { isBand = ∩-isBand
    ; comm = ∩-comm
    }

  ∩-isMonoid : IsMonoid _∩_ U
  ∩-isMonoid = record
    { isSemigroup = ∩-isSemigroup
    ; identity = ∩-identity
    }

  ∩-isCommutativeMonoid : IsCommutativeMonoid _∩_ U
  ∩-isCommutativeMonoid = record
    { isMonoid = ∩-isMonoid
    ; comm = ∩-comm
    }

  ∩-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∩_ U
  ∩-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∩-isCommutativeMonoid
    ; idem = ∩-idem
    }

------------------------------------------------------------------------
-- Algebraic structures of _∪_

  ∪-isMagma : IsMagma _∪_
  ∪-isMagma = record
    { isEquivalence = ≐-isEquivalence
    ; ∙-cong = ∪-cong
    }

  ∪-isSemigroup : IsSemigroup _∪_
  ∪-isSemigroup = record
    { isMagma = ∪-isMagma
    ; assoc = ∪-assoc
    }

  ∪-isBand : IsBand _∪_
  ∪-isBand = record
    { isSemigroup = ∪-isSemigroup
    ; idem = ∪-idem
    }

  ∪-isSemilattice : IsSemilattice _∪_
  ∪-isSemilattice = record
    { isBand = ∪-isBand
    ; comm = ∪-comm
    }

  ∪-isMonoid : IsMonoid _∪_ ∅
  ∪-isMonoid = record
    { isSemigroup = ∪-isSemigroup
    ; identity = ∪-identity
    }

  ∪-isCommutativeMonoid : IsCommutativeMonoid _∪_ ∅
  ∪-isCommutativeMonoid = record
    { isMonoid = ∪-isMonoid
    ; comm = ∪-comm
    }

  ∪-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪_ ∅
  ∪-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪-isCommutativeMonoid
    ; idem = ∪-idem
    }

------------------------------------------------------------------------
-- Algebraic structures of _∩_ and _∪_

  ∪-∩-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _∪_ _∩_ ∅ U
  ∪-∩-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ∪-isCommutativeMonoid
    ; *-cong = ∩-cong
    ; *-assoc = ∩-assoc
    ; *-identity = ∩-identity
    ; distrib = ∩-distrib-∪
    }

  ∪-∩-isSemiring : IsSemiring _∪_ _∩_ ∅ U
  ∪-∩-isSemiring = record
    { isSemiringWithoutAnnihilatingZero = ∪-∩-isSemiringWithoutAnnihilatingZero
    ; zero = ∩-zero
    }

  ∪-∩-isCommutativeSemiring : IsCommutativeSemiring _∪_ _∩_ ∅ U
  ∪-∩-isCommutativeSemiring = record
    { isSemiring = ∪-∩-isSemiring
    ; *-comm = ∩-comm
    }

  ∪-∩-isLattice : IsLattice _∪_ _∩_
  ∪-∩-isLattice = record
    { isEquivalence = ≐-isEquivalence
    ; ∨-comm = ∪-comm
    ; ∨-assoc = ∪-assoc
    ; ∨-cong = ∪-cong
    ; ∧-comm = ∩-comm
    ; ∧-assoc = ∩-assoc
    ; ∧-cong = ∩-cong
    ; absorptive = ∪-∩-absorptive
    }

  ∪-∩-isDistributiveLattice : IsDistributiveLattice _∪_ _∩_
  ∪-∩-isDistributiveLattice = record
    { isLattice = ∪-∩-isLattice
    ; ∨-distrib-∧ = ∪-distrib-∩
    ; ∧-distrib-∨ = ∩-distrib-∪
    }

  ∩-∪-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _∩_ _∪_ U ∅
  ∩-∪-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ∩-isCommutativeMonoid
    ; *-cong = ∪-cong
    ; *-assoc = ∪-assoc
    ; *-identity = ∪-identity
    ; distrib = ∪-distrib-∩
    }

------------------------------------------------------------------------
-- Algebraic bundles of _∩_

  ∩-magma : Magma _ _
  ∩-magma = record
    { isMagma = ∩-isMagma
    }

  ∩-semigroup : Semigroup _ _
  ∩-semigroup = record
    { isSemigroup = ∩-isSemigroup
    }

  ∩-band : Band _ _
  ∩-band = record
    { isBand = ∩-isBand
    }

  ∩-semilattice : Semilattice _ _
  ∩-semilattice = record
    { isSemilattice = ∩-isSemilattice
    }

  ∩-monoid : Monoid _ _
  ∩-monoid = record
    { isMonoid = ∩-isMonoid
    }

  ∩-commutativeMonoid : CommutativeMonoid _ _
  ∩-commutativeMonoid = record
    { isCommutativeMonoid = ∩-isCommutativeMonoid
    }

  ∩-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∩-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∩-isIdempotentCommutativeMonoid
    }

------------------------------------------------------------------------
-- Algebraic bundles of _∪_

  ∪-magma : Magma _ _
  ∪-magma = record
    { isMagma = ∪-isMagma
    }

  ∪-semigroup : Semigroup _ _
  ∪-semigroup = record
    { isSemigroup = ∪-isSemigroup
    }

  ∪-band : Band _ _
  ∪-band = record
    { isBand = ∪-isBand
    }

  ∪-semilattice : Semilattice _ _
  ∪-semilattice = record
    { isSemilattice = ∪-isSemilattice
    }

  ∪-monoid : Monoid _ _
  ∪-monoid = record
    { isMonoid = ∪-isMonoid
    }

  ∪-commutativeMonoid : CommutativeMonoid _ _
  ∪-commutativeMonoid = record
    { isCommutativeMonoid = ∪-isCommutativeMonoid
    }

  ∪-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∪-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∪-isIdempotentCommutativeMonoid
    }

------------------------------------------------------------------------
-- Algebraic bundles of _∩_ and _∪_

  ∪-∩-semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  ∪-∩-semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero = ∪-∩-isSemiringWithoutAnnihilatingZero
    }

  ∪-∩-semiring : Semiring _ _
  ∪-∩-semiring = record
    { isSemiring = ∪-∩-isSemiring
    }

  ∪-∩-commutativeSemiring : CommutativeSemiring _ _
  ∪-∩-commutativeSemiring = record
    { isCommutativeSemiring = ∪-∩-isCommutativeSemiring
    }

  ∪-∩-lattice : Lattice _ _
  ∪-∩-lattice = record
    { isLattice = ∪-∩-isLattice
    }

  ∪-∩-distributiveLattice : DistributiveLattice _ _
  ∪-∩-distributiveLattice = record
    { isDistributiveLattice = ∪-∩-isDistributiveLattice
    }

  ∩-∪-semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  ∩-∪-semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero = ∩-∪-isSemiringWithoutAnnihilatingZero
    }

------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about parities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Properties where

open import Algebra.Bundles
open import Data.Empty
open import Data.Parity.Base
open import Data.Product using (_,_)
open import Data.Sign as Sign using (Sign)
open import Function hiding (Inverse)
open import Level using (0ℓ)
open import Relation.Binary using (Decidable; DecidableEquality; Setoid; DecSetoid; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Algebra.Structures {A = Parity} _≡_
open import Algebra.Definitions {A = Parity} _≡_

open import Algebra.Consequences.Propositional using (comm+distrˡ⇒distrʳ)
open import Algebra.Morphism

module ℙto𝕊 = Algebra.Morphism.Definitions Parity Sign _≡_
module 𝕊toℙ = Algebra.Morphism.Definitions Sign Parity _≡_

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : DecidableEquality Parity
1ℙ ≟ 1ℙ = yes refl
1ℙ ≟ 0ℙ = no λ()
0ℙ ≟ 1ℙ = no λ()
0ℙ ≟ 0ℙ = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Parity

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = isDecEquivalence _≟_

------------------------------------------------------------------------
-- _ᵒ

p≢pᵒ : ∀ p → p ≢ p ᵒ
p≢pᵒ 1ℙ ()
p≢pᵒ 0ℙ ()

ᵒ-inverts : ∀ {p q} → p ᵒ ≡ q → p ≡ q ᵒ
ᵒ-inverts { 1ℙ } { 0ℙ } refl = refl
ᵒ-inverts { 0ℙ } { 1ℙ } refl = refl

ᵒ-involutive : ∀ p → (p ᵒ) ᵒ ≡ p
ᵒ-involutive p = sym (ᵒ-inverts refl)

ᵒ-injective : ∀ {p q} → p ᵒ ≡ q ᵒ → p ≡ q
ᵒ-injective {p} {q} eq = begin
  p       ≡⟨ ᵒ-inverts eq ⟩
  (q ᵒ) ᵒ ≡⟨ ᵒ-involutive q ⟩
  q       ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- ᵒ and _+_

p+pᵒ≡1ℙ : ∀ p → p + p ᵒ ≡ 1ℙ
p+pᵒ≡1ℙ 0ℙ = refl
p+pᵒ≡1ℙ 1ℙ = refl

pᵒ+p≡1ℙ : ∀ p → p ᵒ + p ≡ 1ℙ
pᵒ+p≡1ℙ 0ℙ = refl
pᵒ+p≡1ℙ 1ℙ = refl

------------------------------------------------------------------------
-- ᵒ and _*_

p*pᵒ≡0ℙ : ∀ p → p * p ᵒ ≡ 0ℙ
p*pᵒ≡0ℙ 0ℙ = refl
p*pᵒ≡0ℙ 1ℙ = refl

pᵒ*p≡0ℙ : ∀ p → p ᵒ * p ≡ 0ℙ
pᵒ*p≡0ℙ 0ℙ = refl
pᵒ*p≡0ℙ 1ℙ = refl

------------------------------------------------------------------------
-- _+_

-- Algebraic properties of _+_

p+p≡0ℙ : ∀ p → p + p ≡ 0ℙ
p+p≡0ℙ 0ℙ = refl
p+p≡0ℙ 1ℙ = refl

+-identityˡ : LeftIdentity 0ℙ _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0ℙ _+_
+-identityʳ 1ℙ = refl
+-identityʳ 0ℙ = refl

+-identity : Identity 0ℙ _+_
+-identity = +-identityˡ  , +-identityʳ

+-comm : Commutative _+_
+-comm 0ℙ 0ℙ = refl
+-comm 0ℙ 1ℙ = refl
+-comm 1ℙ 0ℙ = refl
+-comm 1ℙ 1ℙ = refl

+-assoc : Associative _+_
+-assoc 0ℙ 0ℙ _ = refl
+-assoc 0ℙ 1ℙ _ = refl
+-assoc 1ℙ 0ℙ _ = refl
+-assoc 1ℙ 1ℙ 0ℙ = refl
+-assoc 1ℙ 1ℙ 1ℙ = refl

+-cancelʳ-≡ : RightCancellative _+_
+-cancelʳ-≡ _ 1ℙ 1ℙ _  = refl
+-cancelʳ-≡ _ 1ℙ 0ℙ eq = ⊥-elim (p≢pᵒ _ $ sym eq)
+-cancelʳ-≡ _ 0ℙ 1ℙ eq = ⊥-elim (p≢pᵒ _ eq)
+-cancelʳ-≡ _ 0ℙ 0ℙ _  = refl

+-cancelˡ-≡ : LeftCancellative _+_
+-cancelˡ-≡ 1ℙ _ _ eq = ᵒ-injective eq
+-cancelˡ-≡ 0ℙ _ _ eq = eq

+-cancel-≡ : Cancellative _+_
+-cancel-≡ = +-cancelˡ-≡ , +-cancelʳ-≡

+-inverse : Inverse 0ℙ id _+_
+-inverse = p+p≡0ℙ , p+p≡0ℙ

------------------------------------------------------------------------
-- Bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record { _≈_ = _≡_ ; _∙_ = _+_ }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _+_ ; ε = 0ℙ }

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm = +-comm
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-isMonoid : IsMonoid _+_ 0ℙ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-monoid : Monoid 0ℓ 0ℓ
+-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0ℙ
+-0-isCommutativeMonoid = record
   { isMonoid = +-0-isMonoid
   ; comm = +-comm
   }

+-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-isGroup : IsGroup _+_ 0ℙ id
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse = +-inverse
  ; ⁻¹-cong = id
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-isAbelianGroup : IsAbelianGroup _+_ 0ℙ id
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm = +-comm
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-idem : Idempotent _*_
*-idem 0ℙ = refl
*-idem 1ℙ = refl

*-comm : Commutative _*_
*-comm 0ℙ 0ℙ = refl
*-comm 0ℙ 1ℙ = refl
*-comm 1ℙ 0ℙ = refl
*-comm 1ℙ 1ℙ = refl

*-assoc : Associative _*_
*-assoc 0ℙ 0ℙ _ = refl
*-assoc 0ℙ 1ℙ _ = refl
*-assoc 1ℙ 0ℙ _ = refl
*-assoc 1ℙ 1ℙ 0ℙ = refl
*-assoc 1ℙ 1ℙ 1ℙ = refl

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ 0ℙ q r = refl
*-distribˡ-+ 1ℙ 0ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 0ℙ 1ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 1ℙ = refl

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-zeroˡ : LeftZero 0ℙ _*_
*-zeroˡ p = refl

*-zeroʳ : RightZero 0ℙ _*_
*-zeroʳ p = *-comm p 0ℙ

*-zero : Zero 0ℙ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-identityˡ : LeftIdentity 1ℙ _*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity 1ℙ _*_
*-identityʳ 1ℙ = refl
*-identityʳ 0ℙ = refl

*-identity : Identity 1ℙ _*_
*-identity = *-identityˡ  , *-identityʳ

------------------------------------------------------------------------
-- Bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record { _≈_ = _≡_ ; _∙_ = _*_ }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _*_ ; ε = 1ℙ }

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-isCommutativeSemigroup : IsCommutativeSemigroup _*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm = *-comm
  }

*-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
  }

*-1-isMonoid : IsMonoid _*_ 1ℙ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-monoid : Monoid 0ℓ 0ℓ
*-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℙ
*-1-isCommutativeMonoid = record
   { isMonoid = *-1-isMonoid
   ; comm = *-comm
   }

*-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-isSemiring : IsSemiring _+_ _*_ 0ℙ 1ℙ
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-cong = cong₂ _*_
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0ℙ 1ℙ
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-isRing : IsRing _+_ _*_ id 0ℙ 1ℙ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = cong₂ _*_
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ id 0ℙ 1ℙ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

------------------------------------------------------------------------
-- relating Parity and Sign -- where should this go?

{- TODO!!!
   show that ℙto𝕊/𝕊toℙ form an Abelian group isomorphism
   between (Parity, _+_, 0ℙ) and  (𝕊, _*_, 1𝕊)    -}

------------------------------------------------------------------------
-- relating Nat and Parity -- where should this go?

{- TODO!!!
   show that ℕtoℙ is a commutative semiring homomorphism
   between (ℕ, _+_, 0ℕ _*_, 1ℕ) and  (Parity, _+_, 0ℙ, _*_, 1ℙ)
-}

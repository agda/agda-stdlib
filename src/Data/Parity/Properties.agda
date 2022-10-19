------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Properties where

open import Algebra.Bundles
open import Data.Empty
open import Data.Parity.Base
open import Data.Product using (_,_)
open import Data.Sign as Sign using ()
open import Function hiding (Inverse)
open import Level using (0ℓ)
open import Relation.Binary using (Decidable; Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Algebra.Structures {A = Parity} _≡_
open import Algebra.Definitions {A = Parity} _≡_

open import Algebra.Consequences.Propositional using (comm+distrˡ⇒distrʳ)
open import Algebra.Morphism

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : Decidable {A = Parity} _≡_
1ₚ ≟ 1ₚ = yes refl
1ₚ ≟ 0ₚ = no λ()
0ₚ ≟ 1ₚ = no λ()
0ₚ ≟ 0ₚ = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Parity

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- opposite

p≢opposite[p] : ∀ p → p ≢ opposite p
p≢opposite[p] 1ₚ ()
p≢opposite[p] 0ₚ ()

opposite-inverts : ∀ {p q} → opposite p ≡ q → p ≡ opposite q
opposite-inverts { 1ₚ } { 0ₚ } refl = refl
opposite-inverts { 0ₚ } { 1ₚ } refl = refl

opposite-involutive : ∀ p → opposite (opposite p) ≡ p
opposite-involutive p = sym (opposite-inverts refl)

opposite-injective : ∀ {p q} → opposite p ≡ opposite q → p ≡ q
opposite-injective {p} {q} eq = begin
  p ≡⟨ opposite-inverts eq ⟩
  opposite (opposite q) ≡⟨ opposite-involutive q ⟩
  q ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- _+_

-- Algebraic properties of _+_

p+p≡0ₚ : ∀ p → p + p ≡ 0ₚ
p+p≡0ₚ 0ₚ = refl
p+p≡0ₚ 1ₚ = refl

+-identityˡ : LeftIdentity 0ₚ _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0ₚ _+_
+-identityʳ 1ₚ = refl
+-identityʳ 0ₚ = refl

+-identity : Identity 0ₚ _+_
+-identity = +-identityˡ  , +-identityʳ

+-comm : Commutative _+_
+-comm 0ₚ 0ₚ = refl
+-comm 0ₚ 1ₚ = refl
+-comm 1ₚ 0ₚ = refl
+-comm 1ₚ 1ₚ = refl

+-assoc : Associative _+_
+-assoc 0ₚ 0ₚ _ = refl
+-assoc 0ₚ 1ₚ _ = refl
+-assoc 1ₚ 0ₚ _ = refl
+-assoc 1ₚ 1ₚ 0ₚ = refl
+-assoc 1ₚ 1ₚ 1ₚ = refl

+-cancelʳ-≡ : RightCancellative _+_
+-cancelʳ-≡ _ 1ₚ 1ₚ _  = refl
+-cancelʳ-≡ _ 1ₚ 0ₚ eq = ⊥-elim (p≢opposite[p] _ $ sym eq)
+-cancelʳ-≡ _ 0ₚ 1ₚ eq = ⊥-elim (p≢opposite[p] _ eq)
+-cancelʳ-≡ _ 0ₚ 0ₚ _  = refl

+-cancelˡ-≡ : LeftCancellative _+_
+-cancelˡ-≡ 1ₚ _ _ eq = opposite-injective eq
+-cancelˡ-≡ 0ₚ _ _ eq = eq

+-cancel-≡ : Cancellative _+_
+-cancel-≡ = +-cancelˡ-≡ , +-cancelʳ-≡

+-inverse : Inverse 0ₚ id _+_
+-inverse = p+p≡0ₚ , p+p≡0ₚ

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

+-isMonoid : IsMonoid _+_ 0ₚ
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-monoid : Monoid 0ℓ 0ℓ
+-monoid = record
  { isMonoid = +-isMonoid
  }

+-isCommutativeMonoid : IsCommutativeMonoid _+_ 0ₚ
+-isCommutativeMonoid = record
   { isMonoid = +-isMonoid
   ; comm = +-comm
   }

+-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-commutativeMonoid = record
  { isCommutativeMonoid = +-isCommutativeMonoid
  }

+-isGroup : IsGroup _+_ 0ₚ id
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = +-inverse
  ; ⁻¹-cong = id
  }

+-group : Group 0ℓ 0ℓ
+-group = record
  { isGroup = +-isGroup
  }

+-isAbelianGroup : IsAbelianGroup _+_ 0ₚ id
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm = +-comm
  }

+-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-abelianGroup = record
  { isAbelianGroup = +-isAbelianGroup
  }

-- Other properties of _+_

p+opposite[p]≡1ₚ : ∀ p → p + opposite p ≡ 1ₚ
p+opposite[p]≡1ₚ 0ₚ = refl
p+opposite[p]≡1ₚ 1ₚ = refl

opposite[p]+p≡1ₚ : ∀ p → opposite p + p ≡ 1ₚ
opposite[p]+p≡1ₚ 0ₚ = refl
opposite[p]+p≡1ₚ 1ₚ = refl

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-idem : Idempotent _*_
*-idem 0ₚ = refl
*-idem 1ₚ = refl

*-comm : Commutative _*_
*-comm 0ₚ 0ₚ = refl
*-comm 0ₚ 1ₚ = refl
*-comm 1ₚ 0ₚ = refl
*-comm 1ₚ 1ₚ = refl

*-assoc : Associative _*_
*-assoc 0ₚ 0ₚ _ = refl
*-assoc 0ₚ 1ₚ _ = refl
*-assoc 1ₚ 0ₚ _ = refl
*-assoc 1ₚ 1ₚ 0ₚ = refl
*-assoc 1ₚ 1ₚ 1ₚ = refl

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ 0ₚ q r = refl
*-distribˡ-+ 1ₚ 0ₚ 0ₚ = refl
*-distribˡ-+ 1ₚ 0ₚ 1ₚ = refl
*-distribˡ-+ 1ₚ 1ₚ 0ₚ = refl
*-distribˡ-+ 1ₚ 1ₚ 1ₚ = refl

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-zeroˡ : LeftZero 0ₚ _*_
*-zeroˡ p = refl

*-zeroʳ : RightZero 0ₚ _*_
*-zeroʳ p = *-comm p 0ₚ

*-zero : Zero 0ₚ _*_
*-zero = *-zeroˡ , *-zeroʳ

*-identityˡ : LeftIdentity 1ₚ _*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity 1ₚ _*_
*-identityʳ 1ₚ = refl
*-identityʳ 0ₚ = refl

*-identity : Identity 1ₚ _*_
*-identity = *-identityˡ  , *-identityʳ

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

*-isMonoid : IsMonoid _*_ 1ₚ
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-monoid : Monoid 0ℓ 0ℓ
*-monoid = record
  { isMonoid = *-isMonoid
  }

*-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ₚ
*-isCommutativeMonoid = record
   { isMonoid = *-isMonoid
   ; comm = *-comm
   }

*-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-commutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  }

+-*-isSemiring : IsSemiring _+_ _*_ 0ₚ 1ₚ
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-cong = cong₂ _*_
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0ₚ 1ₚ
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isRing : IsRing _+_ _*_ id 0ₚ 1ₚ
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-cong           = cong₂ _*_
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ id 0ₚ 1ₚ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

-- Other properties of _*_

p*opposite[p]≡0ₚ : ∀ p → p * opposite p ≡ 0ₚ
p*opposite[p]≡0ₚ 0ₚ = refl
p*opposite[p]≡0ₚ 1ₚ = refl

opposite[p]*p≡0ₚ : ∀ p → opposite p * p ≡ 0ₚ
opposite[p]*p≡0ₚ 0ₚ = refl
opposite[p]*p≡0ₚ 1ₚ = refl

-- relating Parity and Sign

{-
homoₚₛ-semigroup-morphism : IsSemigroupHomomorphism homoₚₛ
homoₚₛ-semigroup-morphism = record
  { ⟦⟧-cong = ?
  ; ∙-homo  = ?
  }

homoₚₛ-monoid-morphism : IsMonoidHomomorphism homoₚₛ
homoₚₛ-monoid-morphism = record
  { sm-homo = homoₚₛ-semigroup-morphism
  ; ε-homo  = refl
  }
-}

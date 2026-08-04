open import Algebra.Bundles using (Magma; CommutativeRing)
open import Algebra.Bundles.Raw

module Algebra.Polynomial.Properties2
  {ℓ₁ ℓ₂}
  (CR : CommutativeRing ℓ₁ ℓ₂)
  where

import Algebra.Consequences.Setoid as C
  using (comm∧distrʳ⇒distrˡ ; comm∧idʳ⇒idˡ)
import Algebra.Definitions as Def
import Algebra.Polynomial.Poly.Properties2 CR as Poly
open import Algebra.Polynomial.Base2 CR
  using ( Polynomial; _,_;  _≈_; shift; _+_; _*_; _·_
        ; zero; one; -_; refl; sym; trans)
open import Algebra.Properties.AbelianGroup
open import Algebra.Properties.Ring
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsGroup; IsAbelianGroup; IsCommutativeMonoid; IsSemiring 
        ; IsRing; IsCommutativeSemiring; IsCommutativeRing )
open import Data.Nat.Base as ℕ using (ℕ; _⊔_; suc; pred)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using ([]; _∷_)
open import Relation.Binary using (IsEquivalence)

open Polynomial

open CommutativeRing CR
  using (0#; 1#)
  renaming (Carrier to A)

open Def _≈_

private
  variable
    P Q R : Polynomial

--------------------------------------------------------------
-- Algebraic properties of addition

+-identityˡ : LeftIdentity zero  _+_
+-identityˡ P = Poly.+-identityˡ (polynomial P)

+-identityʳ : RightIdentity zero _+_
+-identityʳ P = Poly.+-identityʳ (polynomial P)

+-identity : Identity zero _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : Commutative _+_
+-comm P Q = Poly.+-comm (polynomial P) (polynomial Q)

+-assoc : Associative _+_
+-assoc P Q R
  = Poly.+-assoc (polynomial P) (polynomial Q) (polynomial R) 
  
+-inverseˡ : LeftInverse zero -_ _+_
+-inverseˡ P = Poly.+-inverseˡ (polynomial P)

+-inverseʳ : RightInverse zero -_ _+_
+-inverseʳ P = Poly.+-inverseʳ (polynomial P)

+-inverse : Inverse zero -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

-‿cong : P ≈ Q → - P ≈ - Q
-‿cong = Poly.-‿cong

---------------------------------------------------------------
-- Additive structures

isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

+-isMagma : IsMagma _≈_ _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = Poly.+-cong
  }

+-isSemigroup : IsSemigroup _≈_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm = +-comm
  }

+-isMonoid : IsMonoid _≈_ _+_ zero
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

+-isCommutativeMonoid : IsCommutativeMonoid _≈_ _+_ zero
+-isCommutativeMonoid = record
  { isMonoid = +-isMonoid
  ; comm = +-comm
  }

+-isGroup : IsGroup _≈_ _+_ zero -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = +-inverse
  ;  ⁻¹-cong = -‿cong
  }

+-isAbelianGroup : IsAbelianGroup _≈_ _+_ zero -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm = +-comm
  }

---------------------------------------------------------------
-- Additive bundles
-- Additive bundles

+-rawMagma : Algebra.Bundles.Raw.RawMagma _ _
+-rawMagma = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _∙_ = _+_
  }

*-rawMagma : Algebra.Bundles.Raw.RawMagma _ _
*-rawMagma = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _∙_ = _*_
  }

rawNearSemiring :  Algebra.Bundles.Raw.RawNearSemiring _ _
rawNearSemiring = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = zero
  }

rawSemiring : Algebra.Bundles.Raw.RawSemiring _ _
rawSemiring = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = zero
  ; 1# = one
  }



rawRing : Algebra.Bundles.Raw.RawRing _ _
rawRing = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = zero
  ; 1# = one
  }
  
+-magma : Algebra.Bundles.Magma _ _
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Algebra.Bundles.Semigroup _ _
+-semigroup = record
  { isSemigroup =  +-isSemigroup
  }

+-commutativeSemigroup : Algebra.Bundles.CommutativeSemigroup _ _
+-commutativeSemigroup = record
  {  isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-monoid : Algebra.Bundles.Monoid _ _
+-monoid = record
  { isMonoid =   +-isMonoid
  }

+-commutativeMonoid : Algebra.Bundles.CommutativeMonoid _ _
+-commutativeMonoid = record
  { isCommutativeMonoid =  +-isCommutativeMonoid
  }

+-abelianGroup : Algebra.Bundles.AbelianGroup _ _
+-abelianGroup = record
  { isAbelianGroup =  +-isAbelianGroup
  }

-----------------------------------------------------------------
-- Algebraic properties of multiplication

a·p≈a∷[]*p : (a : A) → (P : Polynomial) → a · P ≈ (1 , (a ∷ [])) * P
a·p≈a∷[]*p a P = Poly.a·p≈a∷[]*p a (polynomial P)

*-comm : Commutative _*_
*-comm P Q = Poly.*-comm (polynomial P) (polynomial Q)

*-identityʳ : RightIdentity one _*_
*-identityʳ P = Poly.*-identityʳ (polynomial P)

*-identityˡ : LeftIdentity one _*_
*-identityˡ = C.comm∧idʳ⇒idˡ (Magma.setoid +-magma) *-comm *-identityʳ

*-identity : Identity one _*_
*-identity =  *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero zero _*_
*-zeroˡ P = Poly.zeroˡ (polynomial P)

*-zeroʳ : RightZero zero _*_
*-zeroʳ P = Poly.zeroʳ (polynomial P)

*-zero : Zero zero _*_
*-zero =  *-zeroˡ , *-zeroʳ

*-assoc : Associative _*_
*-assoc P Q R
  = Poly.*-assoc (polynomial P) (polynomial Q) (polynomial R)

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ P Q R
  = Poly.*-distribʳ-+  (polynomial P) (polynomial Q) (polynomial R)

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+
  = C.comm∧distrʳ⇒distrˡ (Magma.setoid +-magma) Poly.+-cong *-comm *-distribʳ-+ 

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

------------------------------------------------------------------
-- Multiplicative structure

*-isMagma : IsMagma _≈_ _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong  = Poly.*-cong
  }

*-isSemigroup : IsSemigroup _≈_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc = *-assoc
  }

*-isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm = *-comm
  }

*-isMonoid : IsMonoid _≈_ _*_ one
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
  }

*-isCommutativeMonoid : IsCommutativeMonoid _≈_  _*_ one
*-isCommutativeMonoid = record
  { isMonoid = *-isMonoid
  ; comm = *-comm
  }

+-*-isSemiring : IsSemiring _≈_ _+_ _*_ zero one
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-cong = Poly.*-cong
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ zero one  
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isRing : IsRing _≈_  _+_ _*_ -_ zero one  
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-cong           = Poly.*-cong
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }

+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ zero one 
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

---------------------------------------------------------------
-- Multiplicative bundles

*-magma :  Algebra.Bundles.Magma _ _
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Algebra.Bundles.Semigroup _ _
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-commutativeSemigroup : Algebra.Bundles.CommutativeSemigroup _ _
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
  }

*-monoid : Algebra.Bundles.Monoid _ _
*-monoid = record
  { isMonoid = *-isMonoid
  }

*-commutativeMonoid : Algebra.Bundles.CommutativeMonoid _ _
*-commutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  }

+-*-commutativeSemiring : Algebra.Bundles.CommutativeSemiring _ _
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-ring : Algebra.Bundles.Ring _ _
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : Algebra.Bundles.CommutativeRing _ _
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

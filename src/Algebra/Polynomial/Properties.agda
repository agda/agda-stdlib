open import Algebra.Bundles using (Magma; Semiring)

module Algebra.Polynomial.Properties
  {ℓ₁ ℓ₂}
  (SR : Semiring ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw 
import Algebra.Definitions as Def
import Algebra.Polynomial.Poly.Properties SR as Poly
open import Algebra.Polynomial.Base SR
  using ( Polynomial; _,_;  _≈_; shift; _+_; _*_; _·_
        ; zero; one; refl; sym; trans)
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsSemiring; IsCommutativeMonoid 
        )
open import Data.Nat.Base as ℕ using (ℕ; _⊔_; suc; pred)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using ([]; _∷_)
open import Relation.Binary using (IsEquivalence)

open Polynomial

open Semiring SR
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

---------------------------------------------------------------
-- Additive raw bundles
+-rawMagma : Algebra.Bundles.Raw.RawMagma _ _
+-rawMagma = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _∙_ = _+_
  }

+-rawSemiring : Algebra.Bundles.Raw.RawSemiring _ _
+-rawSemiring = record
  { Carrier = Polynomial
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = zero
  ; 1# = one
  }


-- Additive bundles

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

-----------------------------------------------------------------
-- Algebraic properties of multiplication

a·p≈a∷[]*p : (a : A) → (P : Polynomial) → a · P ≈ (1 , (a ∷ [])) * P
a·p≈a∷[]*p a P = Poly.a·p≈a∷[]*p a (polynomial P)

*-identityʳ : RightIdentity one _*_
*-identityʳ P = Poly.*-identityʳ (polynomial P)

*-identityˡ : LeftIdentity one _*_
*-identityˡ P = Poly.*-identityˡ (polynomial P)

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
*-distribˡ-+ P Q R
  = Poly.*-distribˡ-+ (polynomial P) (polynomial Q) (polynomial R)

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

*-isMonoid : IsMonoid _≈_ _*_ one
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
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

*-monoid : Algebra.Bundles.Monoid _ _
*-monoid = record
  { isMonoid = *-isMonoid
  }

+-*-semiring : Semiring _ _
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

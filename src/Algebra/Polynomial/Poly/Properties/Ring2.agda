open import Algebra.Bundles using (Ring)

module Algebra.Polynomial.Poly.Properties.Ring2
  {ℓ₁ ℓ₂} (R : Ring ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw 
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.Ring2 R as P public
  using ( Poly; _+_ ; _*_ ; _·_ ; -_; shift; _≈_; refl; trans; sym
        ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ; module R)
open import Algebra.Polynomial.Poly.Properties.Semiring2 (Ring.semiring R) public
  hiding ( Poly; _+_ ; _*_ ; _·_ ;  shift; _≈_; refl; trans; sym
         ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ )
open import Algebra.Properties.Ring
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsGroup; IsAbelianGroup; IsSemiring; IsCommutativeMonoid 
        ; IsRing)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Product.Base using (_,_)
import Level as L

open Def _≈_

open R
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  ; -_ to -A_)
  using (0#; 1#)

private
  variable
    a b : A
    p : Poly 
    q : Poly 
   
----------------------------------------------------------------------
-- Additive inverse

[-p]+pIsZero : {p : Poly} → IsZero ((- p) + p)
[-p]+pIsZero {p = []} = []
[-p]+pIsZero {p = a ∷ p} = R.-‿inverseˡ a ∷ [-p]+pIsZero

p+[-p]IsZero : {p : Poly} → IsZero (p + (- p))
p+[-p]IsZero {p = []} = []
p+[-p]IsZero {p = a ∷ p} = R.-‿inverseʳ a ∷ p+[-p]IsZero

+-inverseˡ : (p : Poly) → (- p) + p ≈ []
+-inverseˡ [] = refl
+-inverseˡ (a ∷ p)
  = ≈[] ((- (a ∷ p)) + (a ∷ p)) (R.-‿inverseˡ a ∷ [-p]+pIsZero)

+-inverseʳ : (p : Poly) → p + (- p) ≈ []
+-inverseʳ []  = refl
+-inverseʳ (a ∷ p)
  = ≈[] ((a ∷ p) + (- (a ∷ p))) ((R.-‿inverseʳ a) ∷ p+[-p]IsZero)

-⁺ : IsZero p → IsZero (- p)
-⁺ [] = []
-⁺ (a≈0 ∷ p≈0) = x≈ε⇒x⁻¹≈ε R a≈0 ∷ (-⁺ p≈0)

-⁻ : IsZero (- p) → IsZero p
-⁻ {p = []} -p≈0 = -p≈0
-⁻ {p = a ∷ p} (-a≈0 ∷ -p≈0) = x⁻¹≈ε⇒x≈ε R -a≈0 ∷ (-⁻ -p≈0)

-‿cong : p ≈ q → - p ≈ - q
-‿cong ([]≈ q q≈0) = []≈ (- q) (-⁺ q≈0)
-‿cong (≈[] p p≈0) = ≈[] (- p) (-⁺ p≈0)
-‿cong (cons a≈b p≈q) = cons (R.-‿cong a≈b) (-‿cong p≈q)

--------------------------------------------------------------
-- Algebraic properties of addition

+-inverse : Inverse [] -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

---------------------------------------------------------------
-- Additive structures

+-isGroup : IsGroup _≈_ _+_ [] -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = +-inverse
  ;  ⁻¹-cong = -‿cong
  }

+-isAbelianGroup : IsAbelianGroup _≈_ _+_ [] -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm = +-comm
  }

---------------------------------------------------------------
-- Additive bundles

rawRing : Algebra.Bundles.Raw.RawRing _ _
rawRing = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = []
  ; 1# = 1# ∷ []
  }

+-abelianGroup : Algebra.Bundles.AbelianGroup _ _
+-abelianGroup = record
  { isAbelianGroup =  +-isAbelianGroup
  }

------------------------------------------------------------------
-- Multiplicative structure

+-*-isRing : IsRing _≈_  _+_ _*_ -_ [] (1# ∷ [])  
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-cong           = *-cong
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }

---------------------------------------------------------------
-- Multiplicative bundles

+-*-ring : Algebra.Bundles.Ring _ _
+-*-ring = record
  { isRing = +-*-isRing
  }


open import Algebra.Bundles using (AbelianGroup; Ring)

module Algebra.Polynomial.Poly.Properties.Ring
  {ℓ₁ ℓ₂} (R : Ring ℓ₁ ℓ₂)
  where

open import Algebra.Bundles.Raw 
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.Ring R public
  using ( Poly; _+_; _*_; -_; _≈_; IsZero
        ; []≈; ≈[]; cons; 0#; 1#; inject; module R)
open import Algebra.Polynomial.Poly.Properties.Semiring (Ring.semiring R) public
open import Algebra.Properties.Ring
open import Algebra.Structures
  using (IsGroup; IsAbelianGroup; IsRing)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Product.Base using (_,_)

open Def _≈_

open R
  using ()
  renaming (Carrier to A)

private
  variable
    a : A
    p q : Poly 
   
----------------------------------------------------------------------
-- Additive inverse

IsZero-inverseˡ : {p : Poly} → IsZero ((- p) + p)
IsZero-inverseˡ {p = []} = []
IsZero-inverseˡ {p = a ∷ p} = R.-‿inverseˡ a ∷ IsZero-inverseˡ

IsZero-inverseʳ : {p : Poly} → IsZero (p + (- p))
IsZero-inverseʳ {p = []} = []
IsZero-inverseʳ {p = a ∷ p} = R.-‿inverseʳ a ∷ IsZero-inverseʳ

+-inverseˡ : (p : Poly) → (- p) + p ≈ []
+-inverseˡ [] = refl
+-inverseˡ (a ∷ p)
  = ≈[] ((- (a ∷ p)) + (a ∷ p)) (R.-‿inverseˡ a ∷ IsZero-inverseˡ)

+-inverseʳ : (p : Poly) → p + (- p) ≈ []
+-inverseʳ []  = refl
+-inverseʳ (a ∷ p)
  = ≈[] ((a ∷ p) + (- (a ∷ p))) ((R.-‿inverseʳ a) ∷ IsZero-inverseʳ)

IsZero‿-⁺ : IsZero p → IsZero (- p)
IsZero‿-⁺ [] = []
IsZero‿-⁺ (a≈0 ∷ p≈0) = x≈ε⇒x⁻¹≈ε R a≈0 ∷ (IsZero‿-⁺ p≈0)

IsZero‿-⁻ : IsZero (- p) → IsZero p
IsZero‿-⁻ {p = []} -p≈0 = -p≈0
IsZero‿-⁻ {p = a ∷ p} (-a≈0 ∷ -p≈0)
  = x⁻¹≈ε⇒x≈ε R -a≈0 ∷ (IsZero‿-⁻ -p≈0)

-‿cong : p ≈ q → - p ≈ - q
-‿cong ([]≈ q q≈0) = []≈ (- q) (IsZero‿-⁺ q≈0)
-‿cong (≈[] p p≈0) = ≈[] (- p) (IsZero‿-⁺ p≈0)
-‿cong (cons a≈b p≈q) = cons (R.-‿cong a≈b) (-‿cong p≈q)

--------------------------------------------------------------
-- Algebraic properties of addition

+-inverse : Inverse 0# -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

---------------------------------------------------------------
-- Additive structures

+-isGroup : IsGroup _≈_ _+_ 0# -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = +-inverse
  ;  ⁻¹-cong = -‿cong
  }

+-isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm = +-comm
  }

---------------------------------------------------------------
-- Additive bundles

rawRing : RawRing _ _
rawRing = record
  { Carrier = Poly
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = []
  ; 1# = A.1# ∷ []
  }

+-abelianGroup : AbelianGroup _ _
+-abelianGroup = record
  { isAbelianGroup =  +-isAbelianGroup
  }

------------------------------------------------------------------
-- Multiplicative structure

+-*-isRing : IsRing _≈_  _+_ _*_ -_ 0# 1#  
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-cong           = *-cong
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }

---------------------------------------------------------------
-- Multiplicative bundles

+-*-ring : Ring _ _
+-*-ring = record
  { isRing = +-*-isRing
  }


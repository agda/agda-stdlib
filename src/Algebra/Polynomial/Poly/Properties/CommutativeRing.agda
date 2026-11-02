open import Algebra.Bundles using (CommutativeRing)

module Algebra.Polynomial.Poly.Properties.CommutativeRing
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where
  
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.CommutativeRing R as P public
  using ( Poly; _+_ ; _*_ ; _·_ ; -_; shift; _≈_; refl; trans; sym
        ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ; module CR)
open import Algebra.Polynomial.Poly.Properties.Ring (CommutativeRing.ring R) public hiding ( Poly; _+_ ; _*_ ; _·_ ; -_; shift; _≈_; refl; trans; sym
        ; IsZero; []≈ ; ≈[]; cons; zeros-unique; consˡ; consʳ)
open import Algebra.Properties.Ring
open import Algebra.Structures
  using ( IsMagma; IsSemigroup; IsCommutativeSemigroup; IsMonoid
        ; IsGroup; IsAbelianGroup; IsCommutativeMonoid; IsSemiring 
        ; IsRing; IsCommutativeSemiring; IsCommutativeRing )
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Product.Base using (_,_)

open ≈-Reasoning

open CR
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  ; -_ to -A_)
  using (0#; 1#)

open Def _≈_

private
  variable
 
    a b : A
    p : Poly 
    q : Poly 
   
----------------------------------------------------------------------------------
-- Multiplication of polynomials is commutative

*-comm : (p : Poly) → (q : Poly) → p * q ≈ q * p
*-comm [] q  = begin
  [] * (q)
    ≈⟨ p≈[]⇒p*q≈[] q refl ⟩
  []
    ≈⟨ p≈[]⇒q*p≈[] q refl ⟨
  q * [] ∎
*-comm (a ∷ p) [] = begin
  (a ∷ p) * []
    ≈⟨ p≈[]⇒q*p≈[] (a ∷ p) refl ⟩
  []
    ≈⟨ p≈[]⇒p*q≈[] (a ∷ p) refl ⟨
  [] * (a ∷ p) ∎
*-comm (a ∷ p) (b ∷ q) = begin
  (a ∷ p) * (b ∷ q)
    ≈⟨ refl ⟩        
  a · (b ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congˡ (*-comm-lem (a *A b) a) ⟩         
  (a *A b ∷ []) + a · (0# ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congˡ (consˡ (CR.+-congʳ (CR.*-comm a b))) ⟩
  (b *A a ∷ []) + a · (0# ∷ q) + p * (0# ∷ b ∷ q)
    ≈⟨ +-congʳ (step1 (*-comm p (b ∷ q)) (*-comm p q)) ⟩
  (b *A a ∷ []) + a · (0# ∷ q) + ((b · (0# ∷ p)) + (0# ∷ 0# ∷ p * q))
    ≈⟨ step2 ⟩
  ((b *A a ∷ []) + b · (0# ∷ p)) + (a · (0# ∷ q) + (0# ∷ 0# ∷ p * q))
    ≈⟨ step3 ⟩
  (b · (a ∷ p)) + (a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q)))
    ≈⟨ +-congʳ (step4 (*-comm (a ∷ p) q)) ⟨
  (b · (a ∷ p) + q * (0# ∷ a ∷ p))
    ≈⟨ refl ⟩
  (b ∷ q) * (a ∷ p)
    ∎
  where
    *-comm-lem : {p : Poly} → (a b : A) →
                 a ∷ (b · p) ≈ (a ∷ []) + (b · (0# ∷ p))
    *-comm-lem {p = []} a b
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ b)) (CR.+-identityʳ a)))
    *-comm-lem {p = a ∷ p} b c
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ c)) (CR.+-identityʳ b)))
      
    step1 : p * (b ∷ q) ≈ (b ∷ q) * p
          → p * q ≈ q * p
          → p * (0# ∷ b ∷ q) ≈ b · (0# ∷ p) + (0# ∷ 0# ∷ (p * q))
    step1 p*b∷q≈b∷q*p p*q≈q*p = begin
      p * (0# ∷ b ∷ q)
        ≈⟨ *-distrib-shift p (b ∷ q) ⟩
      0# ∷ (p * (b ∷ q))
        ≈⟨ consʳ p*b∷q≈b∷q*p ⟩
      0# ∷ ((b ∷ q) * p)
        ≈⟨ refl ⟩
      0# ∷ (b · p + q * (0# ∷ p))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ 0#)) ⟩ 
      (0# ∷ (b · p)) + (0# ∷ (q * (0# ∷ p)))
        ≈⟨ +-congˡ {r = (0# ∷ (q * (0# ∷ p)))} (·-distrib-shift b p) ⟨
      (b · (0# ∷ p)) + (0# ∷ (q * (0# ∷ p)))
        ≈⟨ +-congʳ {p = b · (0# ∷ p)} (consʳ (*-distrib-shift q p)) ⟩
      b · (0# ∷ p) + (0# ∷ 0# ∷ (q * p))
        ≈⟨ consʳ (+-congʳ (consʳ (p*q≈q*p))) ⟨
      b · (0# ∷ p) + (0# ∷ 0# ∷ (p * q))
        ∎

    step2
      = middleFour (b *A a ∷ []) (a · (0# ∷ q))
        (b · (0# ∷ p)) (0# ∷ 0# ∷ (p * q))
        
    step3
      = +-congˡ {r = a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q))}
        (sym (*-comm-lem {p = p} (b *A a) b))
        
    step4 : (a ∷ p) * q ≈ q * (a ∷ p)
          → q * (0# ∷ a ∷ p) ≈ a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q))
    step4 a∷p*q≈q*a∷p = begin
      q * (0# ∷ a ∷ p)
        ≈⟨ *-distrib-shift q (a ∷ p) ⟩
      0# ∷ (q * (a ∷ p))
        ≈⟨ consʳ a∷p*q≈q*a∷p ⟨
      0# ∷ ((a ∷ p) * q)
        ≈⟨ refl ⟩
      0# ∷ (a · q + p * (0# ∷ q))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ 0#)) ⟩
      (0# ∷ (a · q)) + (0# ∷ (p * (0# ∷ q)))
        ≈⟨ +-congˡ {r = (0# ∷ (p * (0# ∷ q)))} (·-distrib-shift a q) ⟨
      a · (0# ∷ q) + (0# ∷ (p * (0# ∷ q)))
        ≈⟨ +-congʳ {p = a · (0# ∷ q)} (consʳ (*-distrib-shift p q))⟩
      a · (0# ∷ q) + (0# ∷ 0# ∷ (p * q))
        ∎         


------------------------------------------------------------------
-- Multiplicative structure

*-isCommutativeMonoid : IsCommutativeMonoid _≈_  _*_ (1# ∷ [])
*-isCommutativeMonoid = record
  { isMonoid = *-isMonoid
  ; comm = *-comm
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ [] (1# ∷ [])  
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ [] (1# ∷ []) 
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

---------------------------------------------------------------
-- Multiplicative bundles

*-commutativeMonoid : Algebra.Bundles.CommutativeMonoid _ _
*-commutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  }

+-*-commutativeSemiring : Algebra.Bundles.CommutativeSemiring _ _
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-commutativeRing : Algebra.Bundles.CommutativeRing _ _
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }


open import Algebra.Bundles using (CommutativeMonoid; CommutativeSemiring; CommutativeRing)

module Algebra.Polynomial.Poly.Properties.CommutativeRing
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where
  
import Algebra.Definitions as Def
open import Algebra.Polynomial.Poly.Base.CommutativeRing R public
  using (_·_; shift; module CR)
open import Algebra.Polynomial.Poly.Properties.Ring (CommutativeRing.ring R) public
  hiding (module A)
open import Algebra.Properties.Ring
open import Algebra.Structures
  using ( IsCommutativeMonoid; IsCommutativeSemiring; IsCommutativeRing )
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All ; []; _∷_)
open import Data.Product.Base using (_,_)

open ≈-Reasoning

module A = CR
open A
  using ()
  renaming (Carrier to A)

open Def _≈_

private
  variable
 
    a b : A
    p q : Poly 
   
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
  a · (b ∷ q) + p * (A.0# ∷ b ∷ q)
    ≈⟨ +-congˡ (*-comm-lem (a A.* b) a) ⟩         
  (a A.* b ∷ []) + a · (A.0# ∷ q) + p * (A.0# ∷ b ∷ q)
    ≈⟨ +-congˡ (consˡ (CR.+-congʳ (CR.*-comm a b))) ⟩
  (b A.* a ∷ []) + a · (A.0# ∷ q) + p * (A.0# ∷ b ∷ q)
    ≈⟨ +-congʳ (step1 (*-comm p (b ∷ q)) (*-comm p q)) ⟩
  (b A.* a ∷ []) + a · (A.0# ∷ q) + ((b · (A.0# ∷ p)) + (A.0# ∷ A.0# ∷ p * q))
    ≈⟨ step2 ⟩
  ((b A.* a ∷ []) + b · (A.0# ∷ p)) + (a · (A.0# ∷ q) + (A.0# ∷ A.0# ∷ p * q))
    ≈⟨ step3 ⟩
  (b · (a ∷ p)) + (a · (A.0# ∷ q) + (A.0# ∷ A.0# ∷ (p * q)))
    ≈⟨ +-congʳ (step4 (*-comm (a ∷ p) q)) ⟨
  (b · (a ∷ p) + q * (A.0# ∷ a ∷ p))
    ≈⟨ refl ⟩
  (b ∷ q) * (a ∷ p)
    ∎
  where
    *-comm-lem : {p : Poly} → (a b : A) →
                 a ∷ (b · p) ≈ (a ∷ []) + (b · (shift 1 p))
    *-comm-lem {p = []} a b
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ b)) (CR.+-identityʳ a)))
    *-comm-lem {p = a ∷ p} b c
      = consˡ (CR.sym (CR.trans (CR.+-congˡ (CR.zeroʳ c)) (CR.+-identityʳ b)))
      
    step1 : p * (b ∷ q) ≈ (b ∷ q) * p
          → p * q ≈ q * p
          → p * (A.0# ∷ b ∷ q) ≈ b · (A.0# ∷ p) + (A.0# ∷ A.0# ∷ (p * q))
    step1 p*b∷q≈b∷q*p p*q≈q*p = begin
      p * (A.0# ∷ b ∷ q)
        ≈⟨ shift-*ʳ p (b ∷ q) ⟨
      A.0# ∷ (p * (b ∷ q))
        ≈⟨ consʳ p*b∷q≈b∷q*p ⟩
      A.0# ∷ ((b ∷ q) * p)
        ≈⟨ refl ⟩
      A.0# ∷ (b · p + q * (A.0# ∷ p))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ A.0#)) ⟩ 
      (A.0# ∷ (b · p)) + (A.0# ∷ (q * (A.0# ∷ p)))
        ≈⟨ +-congˡ {r = (A.0# ∷ (q * (A.0# ∷ p)))} (·-distrib-shift b p) ⟨
      (b · (A.0# ∷ p)) + (A.0# ∷ (q * (A.0# ∷ p)))
        ≈⟨ +-congʳ {p = b · (A.0# ∷ p)} (consʳ (shift-*ʳ q p)) ⟨
      b · (A.0# ∷ p) + (A.0# ∷ A.0# ∷ (q * p))
        ≈⟨ consʳ (+-congʳ (consʳ (p*q≈q*p))) ⟨
      b · (A.0# ∷ p) + (A.0# ∷ A.0# ∷ (p * q))
        ∎

    step2
      = middleFour (b A.* a ∷ []) (a · (A.0# ∷ q))
        (b · (A.0# ∷ p)) (A.0# ∷ A.0# ∷ (p * q))
        
    step3
      = +-congˡ {r = a · (A.0# ∷ q) + (A.0# ∷ A.0# ∷ (p * q))}
        (sym (*-comm-lem {p = p} (b A.* a) b))
        
    step4 : (a ∷ p) * q ≈ q * (a ∷ p)
          → q * (A.0# ∷ a ∷ p) ≈ a · (A.0# ∷ q) + (A.0# ∷ A.0# ∷ (p * q))
    step4 a∷p*q≈q*a∷p = begin
      q * (A.0# ∷ a ∷ p)
        ≈⟨ shift-*ʳ q (a ∷ p) ⟨
      A.0# ∷ (q * (a ∷ p))
        ≈⟨ consʳ a∷p*q≈q*a∷p ⟨
      A.0# ∷ ((a ∷ p) * q)
        ≈⟨ refl ⟩
      A.0# ∷ (a · q + p * (A.0# ∷ q))
        ≈⟨ consˡ (CR.sym (CR.+-identityʳ A.0#)) ⟩
      (A.0# ∷ (a · q)) + (A.0# ∷ (p * (A.0# ∷ q)))
        ≈⟨ +-congˡ {r = (A.0# ∷ (p * (A.0# ∷ q)))} (·-distrib-shift a q) ⟨
      a · (A.0# ∷ q) + (A.0# ∷ (p * (A.0# ∷ q)))
        ≈⟨ +-congʳ {p = a · (A.0# ∷ q)} (consʳ (shift-*ʳ p q)) ⟨
      a · (A.0# ∷ q) + (A.0# ∷ A.0# ∷ (p * q))
        ∎         

------------------------------------------------------------------
-- Multiplicative structure

*-isCommutativeMonoid : IsCommutativeMonoid _≈_  _*_ 1#
*-isCommutativeMonoid = record
  { isMonoid = *-isMonoid
  ; comm = *-comm
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#  
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1# 
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

---------------------------------------------------------------
-- Multiplicative bundles

*-commutativeMonoid : CommutativeMonoid _ _
*-commutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  }

+-*-commutativeSemiring : CommutativeSemiring _ _
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-commutativeRing : CommutativeRing _ _
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }


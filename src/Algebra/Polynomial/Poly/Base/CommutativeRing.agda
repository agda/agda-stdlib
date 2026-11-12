open import Algebra.Bundles using (CommutativeRing)

module Algebra.Polynomial.Poly.Base.CommutativeRing
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where
  
open import Algebra.Polynomial.Poly.Base.Ring (CommutativeRing.ring R) public 
module CR = CommutativeRing R




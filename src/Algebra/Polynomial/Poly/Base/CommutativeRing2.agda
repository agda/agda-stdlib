open import Algebra.Bundles using (CommutativeRing)

module Algebra.Polynomial.Poly.Base.CommutativeRing2
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where
  
open import Algebra.Polynomial.Poly.Properties.Ring2 (CommutativeRing.ring R) public 
module CR = CommutativeRing R




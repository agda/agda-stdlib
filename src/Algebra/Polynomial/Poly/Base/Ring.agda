open import Algebra.Bundles using (Ring)

module Algebra.Polynomial.Poly.Base.Ring
  {ℓ₁ ℓ₂} (R : Ring ℓ₁ ℓ₂)
  where
  
open import Algebra.Polynomial.Poly.Base.Semiring (Ring.semiring R) public
open import Data.List.Base as List using (List; []; _∷_)

module R = Ring R

private
  variable
    p : Poly 

-- Polynomial subtraction
-_ : Poly → Poly
- p = List.map R.-_ p

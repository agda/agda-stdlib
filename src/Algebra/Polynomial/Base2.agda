open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat.Base as ℕ using (ℕ; _⊔_; suc; pred)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using ([]; _∷_)
import Level as L

module Algebra.Polynomial.Base2
  {ℓ₁ ℓ₂} (CR : CommutativeRing ℓ₁ ℓ₂)
  where

open import Algebra.Polynomial.Poly.Base2 CR as Poly
  using (Poly; zeros)

open CommutativeRing CR
  using (0#; 1#)
  renaming (Carrier to A)

private
  variable
    m n k : ℕ
    p : Poly m
    q : Poly n
    r : Poly k

---------------------------------------------------
-- Types

record Polynomial : Set ℓ₁ where
  constructor _,_
  field
    degree : ℕ
    polynomial : Poly degree

private
  variable
    P Q R : Polynomial

-- Equivalence relation for representations of polynomials
infix 4 _≈_
_≈_ : Polynomial → Polynomial → Set (ℓ₁ L.⊔ ℓ₂)
(m , p) ≈ (n , q) = p Poly.≈ q

refl : P ≈ P
refl = Poly.refl

sym : P ≈ Q → Q ≈ P
sym = Poly.sym

trans : P ≈ Q → Q ≈ R → P ≈ R
trans = Poly.trans

--------------------------------------------------
-- Constants

zero : Polynomial
zero = (0 , [])

one : Polynomial
one = (1 , (1# ∷ []))

---------------------------------------------------
-- Operations

-- Multiply the polynomial by a factor of x
shift : Polynomial → Polynomial
shift (m , p) = (suc m , Poly.shift p)

-- Negation
-_ : Polynomial → Polynomial
- (m , p) = (m , Poly.- p)

-- Scaling
_·_ : A → Polynomial → Polynomial
a · (m , p) = (m , a Poly.· p)

-- Addition
_+_ : Polynomial → Polynomial → Polynomial
(m , p) + (n , q) = (m ⊔ n , p Poly.+ q)

-- Multiplication
_*_ : Polynomial → Polynomial → Polynomial
(m , p) * (n , q) = (pred (m ℕ.+ n) , p Poly.* q)

open import Algebra.Bundles using (Semiring)

module Algebra.Polynomial.Poly.Base.Semiring
  {ℓ₁ ℓ₂} (SR : Semiring ℓ₁ ℓ₂)
  where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base as List hiding ([_])
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc)
import Level as L
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Construct.Add.Infimum
  using (_₋; ⊥₋; [_])
  

module A = Semiring SR
open A
 using ()
 renaming (Carrier to A)
 
infixl 7 _*_
infix 7 _·_
infixl 6 _+_
infix 4 _≈_


private
  variable
   a b : A

-- Polynomial is represented as a list
-- a₀ ∷ a₁ ∷ ⋯ ∷ aₙ ∶ [] represents the polynomial a₀ + a₁x + ⋯ + aₙxⁿ
-- [] represents the zero polynomial 0

Poly : Set ℓ₁
Poly =  List A

private
  variable
    p : Poly 
    q : Poly
    r : Poly

0# : Poly
0# = []

1# : Poly
1# = A.1# ∷ []

-- Scaling a polynomial by a
_·_ : A → Poly → Poly
a · p = List.map (a A.*_) p
  
-- Multiply a polynomial by xⁿ
shift : (n : ℕ) → Poly → Poly
shift 0 p = p
shift (suc n) p = A.0# ∷ shift n p

IsZero : Poly → Set (ℓ₁ L.⊔ ℓ₂)
IsZero = All (A._≈ A.0#)

-- The representation of a polynomial is not unique
-- because we allow coefficients to be zero
-- We define an equivalence relation which takes this into account

data _≈_ : Poly → Poly → Set (ℓ₁ L.⊔ ℓ₂) where
 []≈ : (q : Poly) → IsZero q → [] ≈ q
 ≈[] : (p : Poly) → IsZero p → p ≈ []
 cons : (a A.≈ b) → (p ≈ q) → (a ∷ p) ≈ (b ∷ q)



----------------------------------------------------------------
-- Operations

-- Addition
_+_ : Poly → Poly → Poly
[] + [] = []
[] + (a ∷ p) = a ∷ p
(a ∷ p) + [] = a ∷ p
(a ∷ p) + (b ∷ q) = (a A.+ b) ∷ (p + q)

-- Multiplication
_*_ : Poly → Poly → Poly
_*_ [] p = []
_*_ (a ∷ p) q = (a · q) + (p * (shift 1 q))

-- define a canonical inclusion homomorphism from R to R[x])
inject : A.Carrier → Poly
inject r = r ∷ []


------------------------------------------------------
-- Degree function and polynomial normalization

module _ (_≟0 : ∀ a → Dec (a A.≈ A.0#)) where

-- true degree function of a polynomial
  degree : Poly → ℕ ₋
  degree [] = ⊥₋
  degree (a ∷ p) with degree p
  ... | [ n ] = [ suc n ]
  ... | ⊥₋ with a ≟0
  ...   | yes _ = ⊥₋
  ...   | no  _ = [ 0 ]

-- normalization operation for a polynomial
  normalize : Poly → Poly
  normalize [] = []
  normalize (a ∷ p) with normalize p
  ... | b ∷ q = a ∷ b ∷ q
  ... | [] with a ≟0
  ...   | yes _ = []
  ...   | no _ = a ∷ []

 





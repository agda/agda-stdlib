open import Algebra.Bundles using (Semiring)

module Algebra.Polynomial.Poly.Base.Semiring
  {ℓ₁ ℓ₂} (SR : Semiring ℓ₁ ℓ₂)
  where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base as List
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc)
import Level as L

module SR = Semiring SR
open SR
  renaming
    ( Carrier to A
    ; _≈_ to _≈A_
    ; _+_ to _+A_
    ; _*_ to _*A_
    )
   using (0#; 1#)

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
   
-- Scaling a polynomial by a
_·_ : A → Poly → Poly
a · p = List.map (a *A_) p

--  Multiply a polynomial by x
shift : Poly → Poly
shift p = 0# ∷ p
  
-- Multiply a polynomial by xⁿ
shift-by-n : (n : ℕ) → Poly → Poly
shift-by-n 0 p = p
shift-by-n (suc n) p = 0# ∷ shift-by-n n p

IsZero : Poly → Set (ℓ₁ L.⊔ ℓ₂)
IsZero = All (_≈A 0#)

-- The representation of a polynomial is not unique
-- because we allow coefficients to be zero
-- We define an equivalence relation which takes this into account 

data _≈_ : Poly → Poly → Set (ℓ₁ L.⊔ ℓ₂) where
 []≈ : (q : Poly) → IsZero q → [] ≈ q
 ≈[] : (p : Poly) → IsZero p → p ≈ []
 cons : (a ≈A b) → (p ≈ q) → (a ∷ p) ≈ (b ∷ q)

-- Properties of Polynomial Equality

zeros-unique : IsZero p → IsZero q → p ≈ q
zeros-unique [] [] = []≈ [] []
zeros-unique [] (a≈0 ∷ p≈0) = []≈ (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) [] = ≈[] (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = cons (SR.trans a≈0 (SR.sym b≈0)) (zeros-unique p≈0 q≈0)

IsZero-cong : IsZero p → p ≈ q → IsZero q
IsZero-cong [] ([]≈ q q≈0) = q≈0
IsZero-cong [] (≈[] p p≈0) = p≈0
IsZero-cong (a≈0 ∷ p≈0) (≈[] a∷p a∷p≈0) = []
IsZero-cong (a≈0 ∷ p≈0) (cons a≈b p≈q)
  = (SR.trans (SR.sym a≈b) a≈0) ∷ IsZero-cong p≈0 p≈q

-- _≈_ is an equivalence relation

refl : p ≈ p
refl {p = []} = []≈ [] []
refl {p = a ∷ p} = cons SR.refl refl

sym : p ≈ q → q ≈ p
sym ([]≈ q q≈0) = ≈[] q q≈0
sym (≈[] p p≈0) = []≈ p p≈0
sym (cons a≈b p≈q) = cons (SR.sym a≈b) (sym p≈q)

trans : p ≈ q → q ≈ r → p ≈ r
trans {r = r} ([]≈ q q≈0) q≈r = []≈ r (IsZero-cong q≈0 q≈r) 
trans (≈[] p p≈0) q≈r = zeros-unique p≈0 (IsZero-cong [] q≈r)
trans (cons a≈b p≈q) (≈[] q q≈0)
  = ≈[] _ (IsZero-cong q≈0 (sym (cons a≈b p≈q)))
trans (cons a≈b p≈q) (cons b≈c q≈r)
  = cons (SR.trans a≈b b≈c) (trans p≈q q≈r)

consˡ : (a ≈A b) → (a ∷ p) ≈ (b ∷ p)
consˡ a≈b = cons a≈b refl

consʳ : p ≈ q → (a ∷ p) ≈ (a ∷ q)
consʳ = cons SR.refl
  
----------------------------------------------------------------
-- Operations

-- Addition
_+_ : Poly → Poly → Poly
[] + [] = []
[] + (a ∷ p) = a ∷ p
(a ∷ p) + [] = a ∷ p
(a ∷ p) + (b ∷ q) = (a +A b) ∷ (p + q)

-- Multiplication
_*_ : Poly → Poly → Poly
_*_ [] p = []
_*_ (a ∷ p) q = (a · q) + (p * (0# ∷ q))




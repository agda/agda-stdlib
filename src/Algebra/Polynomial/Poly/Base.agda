open import Algebra.Bundles using (CommutativeRing)

module Algebra.Polynomial.Poly.Base
  {ℓ₁ ℓ₂} (R : CommutativeRing ℓ₁ ℓ₂)
  where

open import Data.Nat.Base as ℕ using (ℕ; suc; pred; _⊔_)
import Data.Nat.Properties as ℕ
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All ; []; _∷_)
import Level as L
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; module ≡-Reasoning)

infix  8 -_
infixl 7 _*_
infix 7 _·_
infixl 6 _+_
infix 4 _≈_

module CR = CommutativeRing R
open CR
  renaming
  ( Carrier to A
  ; _≈_ to _≈A_
  ; _+_ to _+A_
  ; _*_ to _*A_
  ; -_ to -A_)
 using (0#; 1#)

private
  variable
    m n k l : ℕ
    a b c d : A

-- Polynomial of degree most n is represented as a vector of length n + 1
-- a₀ ∷ a₁ ∷ ⋯ ∷ aₙ ∷ [] represents the polynomial a₀ + a₁x + ⋯ + aₙxⁿ

Poly : ℕ → Set ℓ₁
Poly n = Vec A n

private
  variable
    p : Poly m
    q : Poly n
    r : Poly k
    s : Poly l

zeros : (n : ℕ) → Poly n
zeros n = Vec.replicate n (0#)

-- Scaling a polynomial by a
_·_ : A → Poly n → Poly n
a · p  = Vec.map (a *A_) p

-- Multiply a polynomial by a factor of x
shift : Poly n → Poly (suc n)
shift p = 0# ∷ p

IsZero : Poly n → Set (ℓ₁ L.⊔ ℓ₂) 
IsZero = All (_≈A 0#)

-- The additive inverse 
-_ : Poly n → Poly n
- p = Vec.map -A_ p

------------------------------------------------------------------
-- The representation of a polynomial is not unique
-- because we allow coefficients to be zero
-- We define an equivalence relation which takes this into account 

data _≈_ : (Poly m) → (Poly n) → Set (ℓ₁ L.⊔ ℓ₂) where
  []≈  : (q : Poly n) → IsZero q → [] ≈ q
  ≈[]  : (p : Poly m) → IsZero p → p ≈ []
  cons : (a ≈A b) → (p ≈ q) → (a ∷ p) ≈ (b ∷ q)

------------------------------------------------------------------
-- Properties of Polynomial Equality

zeros-unique : IsZero p → IsZero q → p ≈ q
zeros-unique [] [] = []≈ [] []
zeros-unique [] (a≈0 ∷ p≈0) = []≈ (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) [] = ≈[] (_ ∷ _) (a≈0 ∷ p≈0)
zeros-unique (a≈0 ∷ p≈0) (b≈0 ∷ q≈0)
  = cons (CR.trans a≈0 (CR.sym b≈0)) (zeros-unique p≈0 q≈0)

IsZero-cong : IsZero p → p ≈ q → IsZero q
IsZero-cong [] ([]≈ q q≈0) = q≈0
IsZero-cong [] (≈[] p p≈0) = p≈0
IsZero-cong (a≈0 ∷ p≈0) (≈[] a∷p a∷p≈0) = []
IsZero-cong (a≈0 ∷ p≈0) (cons a≈b p≈q)
  = (CR.trans (CR.sym a≈b) a≈0) ∷ IsZero-cong p≈0 p≈q

------------------------------------------------------------------
-- _≈_ is an equivalence relation

refl : p ≈ p
refl {p = []} = []≈ [] []
refl {p = a ∷ p} = cons CR.refl refl

sym : p ≈ q → q ≈ p
sym ([]≈ q q≈0) = ≈[] q q≈0
sym (≈[] p p≈0) = []≈ p p≈0
sym (cons a≈b p≈q) = cons (CR.sym a≈b) (sym p≈q)

trans : p ≈ q → q ≈ r → p ≈ r
trans {r = r} ([]≈ q q≈0) q≈r = []≈ r (IsZero-cong q≈0 q≈r) 
trans (≈[] p p≈0) q≈r = zeros-unique p≈0 (IsZero-cong [] q≈r)
trans (cons a≈b p≈q) (≈[] q q≈0)
  = ≈[] _ (IsZero-cong q≈0 (sym (cons a≈b p≈q)))
trans (cons a≈b p≈q) (cons b≈c q≈r)
  = cons (CR.trans a≈b b≈c) (trans p≈q q≈r)

consˡ : (a ≈A b) → (a ∷ p) ≈ (b ∷ p)
consˡ a≈b = cons a≈b refl

consʳ : p ≈ q → (a ∷ p) ≈ (a ∷ q)
consʳ = cons CR.refl

----------------------------------------------------------------
-- Operations

-- Addition
_+_ : Poly m → Poly n → Poly (m ⊔ n)
[] + [] = []
[] + (a ∷ p) = a ∷ p
(a ∷ p) + [] = a ∷ p
(a ∷ p) + (b ∷ q) = (a +A b) ∷ (p + q)

private
  pred[n+sucm]≡n+m : ∀ n → ∀ m → pred (n ℕ.+ suc m) ≡ n ℕ.+ m
  pred[n+sucm]≡n+m n m = begin
    pred (n ℕ.+ suc m)  ≡⟨ cong pred (ℕ.+-comm n (suc m)) ⟩
    pred (suc m ℕ.+ n)  ≡⟨ ℕ.+-comm m n ⟩
    n ℕ.+ m             ∎
    where open ≡-Reasoning
    
cast-lem : ∀ m → ∀ n → m ⊔ pred (n ℕ.+ suc m) ≡ (n ℕ.+ m)
cast-lem m n = begin
   m ⊔ pred (n ℕ.+ suc m)  ≡⟨ cong (m ⊔_) (pred[n+sucm]≡n+m n m) ⟩
   m ⊔ (n ℕ.+ m)           ≡⟨ ℕ.m≤n⇒m⊔n≡n (ℕ.m≤n+m m n) ⟩
   n ℕ.+ m                 ∎
   where open ≡-Reasoning

-- Multiplication
_*_ : Poly n → Poly m → Poly (pred (n ℕ.+ m))
_*_ {m = m} [] p  = zeros (pred m)
_*_ {suc n} {m} (a ∷ p) q = Vec.cast (cast-lem m n) ((a · q) + (p * (0# ∷ q)))

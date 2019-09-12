{-# OPTIONS --safe --without-K #-}

open import Algebra
open import Data.Bool using (Bool; true; false; T)

module Algebra.Construct.Polynomial.Base {ℓ} (rng : RawRing ℓ) (Zero-C : RawRing.Carrier rng → Bool) where

open import Data.Nat as ℕ          using (ℕ; suc; zero; _≤′_; compare)
open import Relation.Nullary       using (¬_; Dec; yes; no)
open import Level                  using (_⊔_)
open import Data.Empty             using (⊥)
open import Data.Unit              using (⊤; tt)
open import Data.Nat.Properties    using (z≤′n)
open import Data.Product           using (_×_; _,_; map₁; curry; uncurry)
open import Induction.WellFounded  using (Acc; acc)
open import Induction.Nat          using (<′-wellFounded)
open import Data.Fin               using (Fin)

open import Data.List.Kleene
open import Function
open import Algebra.Construct.Polynomial.InjectionIndex
open import Algebra.Construct.Polynomial.Exponentiation rng

infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  inductive
  constructor _Δ_
  field
    coeff : C
    pow   : ℕ
open PowInd public

open RawRing rng

record Poly (n : ℕ) : Set ℓ
data FlatPoly : ℕ → Set ℓ
Coeff : ℕ → Set ℓ
record NonZero (i : ℕ) : Set ℓ
Zero : ∀ {n} → Poly n → Set
Norm : ∀ {i} → Coeff i + → Set

-- A Polynomial is indexed by the number of variables it contains.
infixl 6 _Π_
record Poly n where
  inductive
  constructor _Π_
  field
    {i}  : ℕ
    flat : FlatPoly i
    i≤n  : i ≤′ n

data FlatPoly where
  Κ : Carrier → FlatPoly zero
  Σ : ∀ {n} → (xs : Coeff n +) → .{xn : Norm xs} → FlatPoly (suc n)

-- A list of coefficients, paired with the exponent *gap* from the
-- preceding coefficient. In other words, to represent the
-- polynomial:
--
--   3 + 2x² + 4x⁵ + 2x⁷
--
-- We write:
--
--   [(3,0),(2,1),(4,2),(2,1)]
--
-- Which can be thought of as a representation of the expression:
--
--   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
--
-- This is sparse Horner normal form.

Coeff n = PowInd (NonZero n)

-- We disallow zeroes in the coefficient list. This condition alone
-- is enough to ensure a unique representation for any polynomial.
infixl 6 _≠0
record NonZero i where
  inductive
  constructor _≠0
  field
    poly : Poly i
    .{poly≠0} : ¬ Zero poly

-- This predicate is used (in its negation) to ensure that no
-- coefficient is zero, preventing any trailing zeroes.
Zero (Κ x Π _) = T (Zero-C x)
Zero (Σ _ Π _) = ⊥

-- This predicate is used to ensure that all polynomials are in
-- normal form: if a particular level is constant, than it can
-- be collapsed into the level below it.
Norm (_ Δ zero  & [])  = ⊥
Norm (_ Δ zero  & ∹ _) = ⊤
Norm (_ Δ suc _ & _)   = ⊤
open NonZero public
open Poly public


-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (Σ _ Π _) = no (λ z → z)
zero? (Κ x Π _) with Zero-C x
... | true = yes tt
... | false = no (λ z → z)
{-# INLINE zero? #-}

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓*_ _⍓+_
_⍓*_ : ∀ {n} → Coeff n * → ℕ → Coeff n *
_⍓+_ : ∀ {n} → Coeff n + → ℕ → Coeff n +

[] ⍓* _ = []
(∹ xs) ⍓* i = ∹ xs ⍓+ i

coeff (head (xs ⍓+ i)) = coeff (head xs)
pow (head (xs ⍓+ i)) = pow (head xs) ℕ.+ i
tail (xs ⍓+ i) = tail xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → PowInd (Poly n) → Coeff n * → Coeff n *
x Δ i ∷↓ xs = case zero? x of
  λ { (yes p) → xs ⍓* suc i
    ; (no ¬p) → ∹ _≠0 x {¬p} Δ i & xs
    }
{-# INLINE _∷↓_ #-}

-- Inject a polynomial into a larger polynomoial with more variables
_Π↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
(xs Π i≤n) Π↑ n≤m = xs Π (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)
{-# INLINE _Π↑_ #-}

infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → Coeff i * → suc i ≤′ n → Poly n
[]                        Π↓ i≤n = Κ 0# Π z≤′n
(∹ (x ≠0 Δ zero  & []    )) Π↓ i≤n = x Π↑ i≤n
(∹ (x    Δ zero  & ∹ xs )) Π↓ i≤n = Σ (x Δ zero  & ∹ xs) Π i≤n
(∹ (x    Δ suc j & xs    )) Π↓ i≤n = Σ (x Δ suc j & xs) Π i≤n
{-# INLINE _Π↓_ #-}

--------------------------------------------------------------------------------
-- These folds allow us to abstract over the proofs later: we try to avoid
-- using ∷↓ and Π↓ directly anywhere except here, so if we prove that this fold
-- acts the same on a normalised or non-normalised polynomial, we can prove th
-- same about any operation which uses it.
PolyF : ℕ → Set ℓ
PolyF i = Poly i × Coeff i *

Fold : ℕ → Set ℓ
Fold i = PolyF i → PolyF i

para : ∀ {i} → Fold i → Coeff i + → Coeff i *
para f (x ≠0 Δ i & []) = case f (x , []) of λ { (y , ys) → y Δ i ∷↓ ys }
para f (x ≠0 Δ i & ∹ xs) = case f (x , para f xs) of λ { (y , ys) → y Δ i ∷↓ ys }

poly-map : ∀ {i} → (Poly i → Poly i) → Coeff i + → Coeff i *
poly-map f = para (λ { (x , y) → (f x , y)})
{-# INLINE poly-map #-}

----------------------------------------------------------------------
-- Addition
----------------------------------------------------------------------
-- The reason the following code is so verbose is termination
-- checking. For instance, in the third case for ⊞-coeffs, we call a
-- helper function. Instead, you could conceivably use a with-block
-- (on ℕ.compare p q):
--
-- ⊞-coeffs ((x , p) ∷ xs) ((y , q) ∷ ys) with (ℕ.compare p q)
-- ... | ℕ.less    p k = (x , p) ∷ ⊞-coeffs xs ((y , k) ∷ ys)
-- ... | ℕ.equal   p   = (fst~ x ⊞ fst~ y , p) ∷↓ ⊞-coeffs xs ys
-- ... | ℕ.greater q k = (y , q) ∷ ⊞-coeffs ((x , k) ∷ xs) ys
--
-- However, because the first and third recursive calls each rewrap
-- a list that was already pattern-matched on, the recursive call
-- does not strictly decrease the size of its argument.
--
-- Interestingly, if --without-K is turned off, we don't need the
-- helper function ⊞-coeffs; we could pattern match on _⊞_ directly.
--
-- _⊞_ {zero} (lift x) (lift y) = lift (x + y)
-- _⊞_ {suc n} [] ys = ys
-- _⊞_ {suc n} (x ∷ xs) [] = x ∷ xs
-- _⊞_ {suc n} ((x , p) ∷ xs) ((y , q) ∷ ys) =
--   ⊞-zip (ℕ.compare p q) x xs y ys
mutual
  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  (xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (inj-compare i≤n j≤n) xs ys

  ⊞-match : ∀ {i j n}
        → {i≤n : i ≤′ n}
        → {j≤n : j ≤′ n}
        → InjectionOrdering i≤n j≤n
        → FlatPoly i
        → FlatPoly j
        → Poly n
  ⊞-match (inj-eq i&j≤n)     (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
  ⊞-match (inj-eq i&j≤n)     (Σ (x Δ i & xs)) (Σ (y Δ j & ys)) = ⊞-zip (compare i j) x xs y ys Π↓ i&j≤n
  ⊞-match (inj-lt i≤j-1 j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
  ⊞-match (inj-gt i≤n j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

  ⊞-inj : ∀ {i k}
        → (i ≤′ k)
        → FlatPoly i
        → Coeff k +
        → Coeff k *
  ⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero & ys) = ⊞-match (inj-compare j≤k i≤k) y xs Δ zero ∷↓ ys
  ⊞-inj i≤k xs (y Δ suc j & ys) = xs Π i≤k Δ zero ∷↓ ∹ y Δ j & ys 

  ⊞-coeffs : ∀ {n} → Coeff n * → Coeff n * → Coeff n *
  ⊞-coeffs (∹ x Δ i & xs) ys = ⊞-zip-r x i xs ys
  ⊞-coeffs [] ys = ys

  ⊞-zip : ∀ {p q n}
        → ℕ.Ordering p q
        → NonZero n
        → Coeff n *
        → NonZero n
        → Coeff n *
        → Coeff n *
  ⊞-zip (ℕ.less    i k) x xs y ys = ∹ x Δ i & ⊞-zip-r y k ys xs
  ⊞-zip (ℕ.greater j k) x xs y ys = ∹ y Δ j & ⊞-zip-r x k xs ys
  ⊞-zip (ℕ.equal   i  ) x xs y ys = (x .poly ⊞ y .poly) Δ i ∷↓ ⊞-coeffs xs ys

  ⊞-zip-r : ∀ {n} → NonZero n → ℕ → Coeff n * → Coeff n * → Coeff n *
  ⊞-zip-r x i xs [] = ∹ x Δ i & xs
  ⊞-zip-r x i xs (∹ y Δ j & ys) = ⊞-zip (compare i j) x xs y ys
{-# INLINE ⊞-zip #-}

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

⊟-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n
⊟-step (acc wf) (Κ x  Π i≤n) = Κ (- x) Π i≤n
⊟-step (acc wf) (Σ xs Π i≤n) = poly-map (⊟-step (wf _ i≤n)) xs Π↓ i≤n

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step (<′-wellFounded _)
{-# INLINE ⊟_ #-}

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  ⊠-step′ : ∀ {n} → Acc _<′_ n → Poly n → Poly n → Poly n
  ⊠-step′ a (x Π i≤n) = ⊠-step a x i≤n

  ⊠-step : ∀ {i n} → Acc _<′_ n → FlatPoly i → i ≤′ n → Poly n → Poly n
  ⊠-step a (Κ x) _ = ⊠-Κ a x
  ⊠-step a (Σ xs)  = ⊠-Σ a xs

  ⊠-Κ : ∀ {n} → Acc _<′_ n → Carrier → Poly n → Poly n
  ⊠-Κ (acc _ ) x (Κ y  Π i≤n) = Κ (x * y) Π i≤n
  ⊠-Κ (acc wf) x (Σ xs Π i≤n) = ⊠-Κ-inj (wf _ i≤n) x xs Π↓ i≤n

  ⊠-Σ : ∀ {i n} → Acc _<′_ n → Coeff i + → i <′ n → Poly n → Poly n
  ⊠-Σ (acc wf) xs i≤n (Σ ys Π j≤n) = ⊠-match  (acc wf) (inj-compare i≤n j≤n) xs ys
  ⊠-Σ (acc wf) xs i≤n (Κ y Π _) = ⊠-Κ-inj (wf _ i≤n) y xs Π↓ i≤n

  ⊠-Κ-inj : ∀ {i}  → Acc _<′_ i → Carrier → Coeff i + → Coeff i *
  ⊠-Κ-inj a x xs = poly-map (⊠-Κ a x) (xs)

  ⊠-Σ-inj : ∀ {i k}
          → Acc _<′_ k
          → i <′ k
          → Coeff i +
          → Poly k
          → Poly k
  ⊠-Σ-inj (acc wf) i≤k x (Σ y Π j≤k) = ⊠-match (acc wf) (inj-compare i≤k j≤k) x y
  ⊠-Σ-inj (acc wf) i≤k x (Κ y Π j≤k) = ⊠-Κ-inj (wf _ i≤k) y x Π↓ i≤k

  ⊠-match : ∀ {i j n}
          → Acc _<′_ n
          → {i≤n : i <′ n}
          → {j≤n : j <′ n}
          → InjectionOrdering i≤n j≤n
          → Coeff i +
          → Coeff j +
          → Poly n
  ⊠-match (acc wf) (inj-eq i&j≤n)     xs ys = ⊠-coeffs (wf _ i&j≤n) xs ys               Π↓ i&j≤n
  ⊠-match (acc wf) (inj-lt i≤j-1 j≤n) xs ys = poly-map (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs) (ys) Π↓ j≤n
  ⊠-match (acc wf) (inj-gt i≤n j≤i-1) xs ys = poly-map (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys) (xs) Π↓ i≤n

  ⊠-coeffs : ∀ {n} → Acc _<′_ n → Coeff n + → Coeff n + → Coeff n *
  ⊠-coeffs a (xs) (y ≠0 Δ j & []) = poly-map (⊠-step′ a y) (xs) ⍓* j
  ⊠-coeffs a (xs) (y ≠0 Δ j & ∹ ys) = para (⊠-cons a y ys) (xs) ⍓* j

  ⊠-cons : ∀ {n}
          → Acc _<′_ n
          → Poly n
          → Coeff n +
          → Fold n
  -- ⊠-cons a y [] (x Π j≤n , xs) = ⊠-step a x j≤n y , xs
  ⊠-cons a y ys (x Π j≤n , xs) =
    ⊠-step a x j≤n y , ⊞-coeffs (poly-map (⊠-step a x j≤n) ys) xs
{-# INLINE ⊠-Κ #-}
{-# INLINE ⊠-coeffs #-}
{-# INLINE ⊠-cons #-}

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ = ⊠-step′ (<′-wellFounded _)
{-# INLINE _⊠_ #-}

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x Π z≤′n
{-# INLINE κ #-}

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# Δ 1 ∷↓ []) Π↓ Fin⇒≤ i
{-# INLINE ι #-}

----------------------------------------------------------------------
-- Exponentiation
----------------------------------------------------------------------
-- We try very hard to never do things like multiply by 1
-- unnecessarily. That's what all the weirdness here is for.
⊡-mult : ∀ {n} → ℕ → Poly n → Poly n
⊡-mult zero xs = xs
⊡-mult (suc n) xs = ⊡-mult n xs ⊠ xs

_⊡_+1 : ∀ {n} → Poly n → ℕ → Poly n
(Κ x  Π i≤n) ⊡ i +1  = Κ (x ^ i +1) Π i≤n
(Σ (x Δ j & []) Π i≤n) ⊡ i +1  = x .poly ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] Π↓ i≤n
xs@(Σ (_ & ∹ _) Π i≤n) ⊡ i +1  = ⊡-mult i xs

infixr 8 _⊡_
_⊡_ : ∀ {n} → Poly n → ℕ → Poly n
_ ⊡ zero = κ 1#
xs ⊡ suc i = xs ⊡ i +1
{-# INLINE _⊡_ #-}

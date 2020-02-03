------------------------------------------------------------------------
-- The Agda standard library
--
-- Sparse polynomials in a commutative ring, encoded in Horner normal
-- form.
--
-- Horner normal form encodes a polynomial as a list of coefficients.
-- As an example take the polynomial:
--
--   3 + 2x² + 4x⁵ + 2x⁷
--
-- Then expand it out, filling in the missing coefficients:
--
--   3x⁰ + 0x¹ + 2x² + 0x³ + 0x⁴ + 4x⁵ + 0x⁶ + 2x⁷
--
-- And then encode that as a list:
--
--   [3, 0, 2, 0, 0, 4, 0, 2]
--
-- The representation we use here is optimised from the above. First,
-- we remove the zero terms, and add a "gap" index next to every
-- coefficient:
--
--   [(3,0),(2,1),(4,2),(2,1)]
--
-- Which can be thought of as a representation of the expression:
--
--   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
--
-- This is "sparse" Horner normal form.
--
-- The second optimisation deals with representing multiple variables
-- in a polynomial. The standard trick is to encode a polynomial in n
-- variables as a polynomial with coefficients in n-1 variables,
-- recursing until you hit 0 which is simply the type of the coefficient
-- itself.
--
-- We again encode "gaps" here, with the injection index. Since the
-- number of variables in a polynomial is contained in its type,
-- however, operations on this gap are type-relevant, so it's not
-- convenient to simply use ℕ. We use _≤′_ instead.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Base
  {ℓ₁ ℓ₂} (coeffs : RawCoeff ℓ₁ ℓ₂) where

open RawCoeff coeffs

open import Data.Bool              using (Bool; true; false; T)
open import Data.Empty             using (⊥)
open import Data.Fin.Base as Fin        using (Fin; zero; suc)
open import Data.List.Kleene
open import Data.Nat.Base as ℕ          using (ℕ; suc; zero; _≤′_; compare; ≤′-refl; ≤′-step; _<′_)
open import Data.Nat.Properties    using (z≤′n; ≤′-trans)
open import Data.Nat.Induction
open import Data.Product           using (_×_; _,_; map₁; curry; uncurry)
open import Data.Unit              using (⊤; tt)
open import Function.Base
open import Relation.Nullary       using (¬_; Dec; yes; no)

open import Algebra.Operations.Ring rawRing

------------------------------------------------------------------------
-- Injection indices.
------------------------------------------------------------------------

-- First, we define comparisons on _≤′_.
-- The following is analagous to Ordering and compare from
-- Data.Nat.Base.
data InjectionOrdering {n : ℕ} : ∀ {i j} (i≤n : i ≤′ n) (j≤n : j ≤′ n) → Set
                      where
  inj-lt : ∀ {i j-1} (i≤j-1 : i ≤′ j-1) (j≤n : suc j-1 ≤′ n) →
           InjectionOrdering (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) j≤n

  inj-gt : ∀ {i-1 j} (i≤n : suc i-1 ≤′ n) (j≤i-1 : j ≤′ i-1) →
           InjectionOrdering i≤n (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n)

  inj-eq : ∀ {i} (i≤n : i ≤′ n) →
           InjectionOrdering i≤n i≤n

inj-compare : ∀ {i j n} (x : i ≤′ n) (y : j ≤′ n) → InjectionOrdering x y
inj-compare ≤′-refl     ≤′-refl     = inj-eq ≤′-refl
inj-compare ≤′-refl     (≤′-step y) = inj-gt ≤′-refl y
inj-compare (≤′-step x) ≤′-refl     = inj-lt x ≤′-refl
inj-compare (≤′-step x) (≤′-step y) = case inj-compare x y of
    λ { (inj-lt i≤j-1 y) → inj-lt i≤j-1 (≤′-step y)
      ; (inj-gt x j≤i-1) → inj-gt (≤′-step x) j≤i-1
      ; (inj-eq x)       → inj-eq (≤′-step x)
      }

-- The "space" above a Fin n is the number of unique "Fin n"s greater
-- than or equal to it.
space : ∀ {n} → Fin n → ℕ
space f = suc (go f)
  where
  go : ∀ {n} → Fin n → ℕ
  go {suc n} Fin.zero = n
  go (Fin.suc x) = go x

space≤′n : ∀ {n} (x : Fin n) → space x ≤′ n
space≤′n zero    = ≤′-refl
space≤′n (suc x) = ≤′-step (space≤′n x)

-------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------

infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  constructor _Δ_
  field
    coeff : C
    pow   : ℕ
open PowInd public


record Poly (n : ℕ) : Set ℓ₁
data FlatPoly : ℕ → Set ℓ₁
Coeff : ℕ → Set ℓ₁
record NonZero (i : ℕ) : Set ℓ₁
Zero : ∀ {n} → Poly n → Set
Normalised : ∀ {i} → Coeff i + → Set

-- A Polynomial is indexed by the number of variables it contains.
infixl 6 _⊐_
record Poly n where
  inductive
  constructor _⊐_
  field
    {i}  : ℕ
    flat : FlatPoly i
    i≤n  : i ≤′ n

data FlatPoly where
  Κ : Carrier → FlatPoly zero
  ⅀ : ∀ {n} (xs : Coeff n +) {xn : Normalised xs} → FlatPoly (suc n)


Coeff n = PowInd (NonZero n)

-- We disallow zeroes in the coefficient list. This condition alone
-- is enough to ensure a unique representation for any polynomial.
infixl 6 _≠0
record NonZero i where
  inductive
  constructor _≠0
  field
    poly      : Poly i
    .{poly≠0} : ¬ Zero poly

-- This predicate is used (in its negation) to ensure that no
-- coefficient is zero, preventing any trailing zeroes.
Zero (Κ x ⊐ _) = T (isZero x)
Zero (⅀ _ ⊐ _) = ⊥

-- This predicate is used to ensure that all polynomials are in
-- normal form: if a particular level is constant, then it can
-- be collapsed into the level below it.
Normalised (_ Δ zero  & [])  = ⊥
Normalised (_ Δ zero  & ∹ _) = ⊤
Normalised (_ Δ suc _ & _)   = ⊤
open NonZero public
open Poly public

----------------------------------------------------------------------
-- Special operations

-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (⅀ _ ⊐ _) = no id
zero? (Κ x ⊐ _) with isZero x
... | true  = yes tt
... | false = no  id
{-# INLINE zero? #-}

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓*_ _⍓+_
_⍓*_ : ∀ {n} → Coeff n * → ℕ → Coeff n *
_⍓+_ : ∀ {n} → Coeff n + → ℕ → Coeff n +

[] ⍓* _ = []
(∹ xs) ⍓* i = ∹ xs ⍓+ i

coeff (head (xs ⍓+ i)) = coeff (head xs)
pow   (head (xs ⍓+ i)) = pow (head xs) ℕ.+ i
tail  (xs ⍓+ i)        = tail xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → PowInd (Poly n) → Coeff n * → Coeff n *
x Δ i ∷↓ xs = case zero? x of
  λ { (yes p) → xs ⍓* suc i
    ; (no ¬p) → ∹ _≠0 x {¬p} Δ i & xs
    }
{-# INLINE _∷↓_ #-}

-- Inject a polynomial into a larger polynomial with more variables
_⊐↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
(xs ⊐ i≤n) ⊐↑ n≤m = xs ⊐ (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)
{-# INLINE _⊐↑_ #-}

infixr 4 _⊐↓_
_⊐↓_ : ∀ {i n} → Coeff i * → suc i ≤′ n → Poly n
[]                        ⊐↓ i≤n = Κ 0# ⊐ z≤′n
(∹ (x ≠0 Δ zero  & []  )) ⊐↓ i≤n = x ⊐↑ i≤n
(∹ (x    Δ zero  & ∹ xs)) ⊐↓ i≤n = ⅀ (x Δ zero  & ∹ xs) ⊐ i≤n
(∹ (x    Δ suc j & xs  )) ⊐↓ i≤n = ⅀ (x Δ suc j & xs)   ⊐ i≤n
{-# INLINE _⊐↓_ #-}

----------------------------------------------------------------------
-- Standard operations
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Folds

-- These folds allow us to abstract over the proofs later: we try to avoid
-- using ∷↓ and ⊐↓ directly anywhere except here, so if we prove that this fold
-- acts the same on a normalised or non-normalised polynomial, we can prove th
-- same about any operation which uses it.

PolyF : ℕ → Set ℓ₁
PolyF i = Poly i × Coeff i *

Fold : ℕ → Set ℓ₁
Fold i = PolyF i → PolyF i

para : ∀ {i} → Fold i → Coeff i + → Coeff i *
para f (x ≠0 Δ i & [])   = case f (x , [])        of λ {(y , ys) → y Δ i ∷↓ ys}
para f (x ≠0 Δ i & ∹ xs) = case f (x , para f xs) of λ {(y , ys) → y Δ i ∷↓ ys}

poly-map : ∀ {i} → (Poly i → Poly i) → Coeff i + → Coeff i *
poly-map f = para (map₁ f)
{-# INLINE poly-map #-}

----------------------------------------------------------------------
-- Addition

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
-- _⊞_ {suc n} ((x , p) ∷ xs) ((y , q) ∷ ys) = ⊞-zip (ℕ.compare p q) x xs y ys

mutual
  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  (xs ⊐ i≤n) ⊞ (ys ⊐ j≤n) = ⊞-match (inj-compare i≤n j≤n) xs ys

  ⊞-match : ∀ {i j n}
        → {i≤n : i ≤′ n}
        → {j≤n : j ≤′ n}
        → InjectionOrdering i≤n j≤n
        → FlatPoly i
        → FlatPoly j
        → Poly n
  ⊞-match (inj-eq i&j≤n)     (Κ x)  (Κ y)  = Κ (x + y)         ⊐  i&j≤n
  ⊞-match (inj-eq i&j≤n)     (⅀ (x Δ i & xs)) (⅀ (y Δ j & ys)) = ⊞-zip (compare i j) x xs y ys ⊐↓ i&j≤n
  ⊞-match (inj-lt i≤j-1 j≤n)  xs    (⅀ ys) = ⊞-inj i≤j-1 xs ys ⊐↓ j≤n
  ⊞-match (inj-gt i≤n j≤i-1) (⅀ xs)  ys    = ⊞-inj j≤i-1 ys xs ⊐↓ i≤n

  ⊞-inj : ∀ {i k}
        → (i ≤′ k)
        → FlatPoly i
        → Coeff k +
        → Coeff k *
  ⊞-inj i≤k xs (y ⊐ j≤k ≠0 Δ zero  & ys) = ⊞-match (inj-compare j≤k i≤k) y xs Δ zero ∷↓ ys
  ⊞-inj i≤k xs (y          Δ suc j & ys) = xs ⊐ i≤k Δ zero ∷↓ ∹ y Δ j & ys

  ⊞-coeffs : ∀ {n} → Coeff n * → Coeff n * → Coeff n *
  ⊞-coeffs (∹ x Δ i & xs) ys = ⊞-zip-r x i xs ys
  ⊞-coeffs []             ys = ys

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
  {-# INLINE ⊞-zip #-}

  ⊞-zip-r : ∀ {n} → NonZero n → ℕ → Coeff n * → Coeff n * → Coeff n *
  ⊞-zip-r x i xs [] = ∹ x Δ i & xs
  ⊞-zip-r x i xs (∹ y Δ j & ys) = ⊞-zip (compare i j) x xs y ys

----------------------------------------------------------------------
-- Negation

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

⊟-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n
⊟-step (acc wf) (Κ x  ⊐ i≤n) = Κ (- x) ⊐ i≤n
⊟-step (acc wf) (⅀ xs ⊐ i≤n) = poly-map (⊟-step (wf _ i≤n)) xs ⊐↓ i≤n

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step (<′-wellFounded _)
{-# INLINE ⊟_ #-}

----------------------------------------------------------------------
-- Multiplication

mutual
  ⊠-step′ : ∀ {n} → Acc _<′_ n → Poly n → Poly n → Poly n
  ⊠-step′ a (x ⊐ i≤n) = ⊠-step a x i≤n

  ⊠-step : ∀ {i n} → Acc _<′_ n → FlatPoly i → i ≤′ n → Poly n → Poly n
  ⊠-step a (Κ x) _ = ⊠-Κ a x
  ⊠-step a (⅀ xs)  = ⊠-⅀ a xs

  ⊠-Κ : ∀ {n} → Acc _<′_ n → Carrier → Poly n → Poly n
  ⊠-Κ (acc _ ) x (Κ y  ⊐ i≤n) = Κ (x * y) ⊐ i≤n
  ⊠-Κ (acc wf) x (⅀ xs ⊐ i≤n) = ⊠-Κ-inj (wf _ i≤n) x xs ⊐↓ i≤n
  {-# INLINE ⊠-Κ #-}

  ⊠-⅀ : ∀ {i n} → Acc _<′_ n → Coeff i + → i <′ n → Poly n → Poly n
  ⊠-⅀ (acc wf) xs i≤n (⅀ ys ⊐ j≤n) = ⊠-match  (acc wf) (inj-compare i≤n j≤n) xs ys
  ⊠-⅀ (acc wf) xs i≤n (Κ y ⊐ _)    = ⊠-Κ-inj (wf _ i≤n) y xs ⊐↓ i≤n

  ⊠-Κ-inj : ∀ {i}  → Acc _<′_ i → Carrier → Coeff i + → Coeff i *
  ⊠-Κ-inj a x xs = poly-map (⊠-Κ a x) (xs)

  ⊠-⅀-inj : ∀ {i k}
          → Acc _<′_ k
          → i <′ k
          → Coeff i +
          → Poly k
          → Poly k
  ⊠-⅀-inj (acc wf) i≤k x (⅀ y ⊐ j≤k) = ⊠-match (acc wf) (inj-compare i≤k j≤k) x y
  ⊠-⅀-inj (acc wf) i≤k x (Κ y ⊐ j≤k) = ⊠-Κ-inj (wf _ i≤k) y x ⊐↓ i≤k

  ⊠-match : ∀ {i j n}
          → Acc _<′_ n
          → {i≤n : i <′ n}
          → {j≤n : j <′ n}
          → InjectionOrdering i≤n j≤n
          → Coeff i +
          → Coeff j +
          → Poly n
  ⊠-match (acc wf) (inj-eq i&j≤n)     xs ys = ⊠-coeffs (wf _ i&j≤n) xs ys               ⊐↓ i&j≤n
  ⊠-match (acc wf) (inj-lt i≤j-1 j≤n) xs ys = poly-map (⊠-⅀-inj (wf _ j≤n) i≤j-1 xs) (ys) ⊐↓ j≤n
  ⊠-match (acc wf) (inj-gt i≤n j≤i-1) xs ys = poly-map (⊠-⅀-inj (wf _ i≤n) j≤i-1 ys) (xs) ⊐↓ i≤n

  ⊠-coeffs : ∀ {n} → Acc _<′_ n → Coeff n + → Coeff n + → Coeff n *
  ⊠-coeffs a (xs) (y ≠0 Δ j & [])   = poly-map (⊠-step′ a y) (xs) ⍓* j
  ⊠-coeffs a (xs) (y ≠0 Δ j & ∹ ys) = para (⊠-cons a y ys) (xs) ⍓* j
  {-# INLINE ⊠-coeffs #-}

  ⊠-cons : ∀ {n}
          → Acc _<′_ n
          → Poly n
          → Coeff n +
          → Fold n
  ⊠-cons a y ys (x ⊐ j≤n , xs) =
    ⊠-step a x j≤n y , ⊞-coeffs (poly-map (⊠-step a x j≤n) ys) xs
  {-# INLINE ⊠-cons #-}

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ = ⊠-step′ (<′-wellFounded _)
{-# INLINE _⊠_ #-}

----------------------------------------------------------------------
-- Constants and variables

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x ⊐ z≤′n
{-# INLINE κ #-}

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# Δ 1 ∷↓ []) ⊐↓ space≤′n i
{-# INLINE ι #-}

----------------------------------------------------------------------
-- Exponentiation

-- We try very hard to never do things like multiply by 1
-- unnecessarily. That's what all the weirdness here is for.

⊡-mult : ∀ {n} → ℕ → Poly n → Poly n
⊡-mult zero    xs = xs
⊡-mult (suc n) xs = ⊡-mult n xs ⊠ xs

_⊡_+1 : ∀ {n} → Poly n → ℕ → Poly n
(Κ x  ⊐ i≤n)           ⊡ i +1  = Κ (x ^ i +1) ⊐ i≤n
(⅀ (x Δ j & []) ⊐ i≤n) ⊡ i +1  = x .poly ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⊐↓ i≤n
xs@(⅀ (_ & ∹ _) ⊐ i≤n) ⊡ i +1  = ⊡-mult i xs

infixr 8 _⊡_
_⊡_ : ∀ {n} → Poly n → ℕ → Poly n
_  ⊡ zero  = κ 1#
xs ⊡ suc i = xs ⊡ i +1
{-# INLINE _⊡_ #-}

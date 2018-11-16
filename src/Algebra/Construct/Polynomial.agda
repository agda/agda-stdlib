------------------------------------------------------------------------
-- The Agda standard library
--
-- Multivariate Polynomials over a ring of coefficients
------------------------------------------------------------------------

open import Algebra

module Algebra.Construct.Polynomial {r} (K : RawRing r) where

private module K = RawRing K

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin)

infix  9 :-_
infixr 9 _:×_ _:^_
infixl 8 _:*_
infixl 7 _:+_ _:-_

------------------------------------------------------------------------
-- Polynomials

data Op : Set where
  [+] : Op
  [*] : Op

-- The polynomials are indexed by the number of variables.

data Polynomial (m : ℕ) : Set r where
  op   : (o : Op) (p₁ p₂ : Polynomial m) → Polynomial m
  con  : (c : K.Carrier) → Polynomial m
  var  : (x : Fin m) → Polynomial m
  _:^_ : (p : Polynomial m) (n : ℕ) → Polynomial m
  :-_  : (p : Polynomial m) → Polynomial m

-- Short-hand notation.

_:+_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
_:+_ = op [+]

_:*_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
_:*_ = op [*]

_:-_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
x :- y = x :+ :- y

_:×_ : ∀ {n} → ℕ → Polynomial n → Polynomial n
zero  :× p = con K.0#
suc m :× p = p :+ m :× p

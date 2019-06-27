------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

module Data.Integer.Base where

open import Data.Nat.Base as ℕ
  using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Sign as Sign using (Sign) renaming (_*_ to _S*_)
open import Function
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix  8 -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊖_ _⊔_
infix  4 _≤_ _≥_ _<_ _>_ _≰_ _≱_ _≮_ _≯_

------------------------------------------------------------------------
-- The types

open import Agda.Builtin.Int public
  using ()
  renaming
  ( Int    to ℤ
  ; pos    to +_      -- "+ n"      stands for "n"
  ; negsuc to -[1+_]  -- "-[1+ n ]" stands for "- (1 + n)"
  )

------------------------------------------------------------------------
-- Some additional patterns that provide symmetry around 0

pattern +0       = + 0
pattern +[1+_] n = + (ℕ.suc n)

------------------------------------------------------------------------
-- Ordering

data _≤_ : ℤ → ℤ → Set where
  -≤- : ∀ {m n} → (n≤m : n ℕ.≤ m) → -[1+ m ] ≤ -[1+ n ]
  -≤+ : ∀ {m n} → -[1+ m ] ≤ + n
  +≤+ : ∀ {m n} → (m≤n : m ℕ.≤ n) → + m ≤ + n

data _<_ : ℤ → ℤ → Set where
  -<- : ∀ {m n} → (n<m : n ℕ.< m) → -[1+ m ] < -[1+ n ]
  -<+ : ∀ {m n} → -[1+ m ] < + n
  +<+ : ∀ {m n} → (m<n : m ℕ.< n) → + m < + n

_≥_ : Rel ℤ 0ℓ
x ≥ y = y ≤ x

_>_ : Rel ℤ 0ℓ
x > y = y < x

_≰_ : Rel ℤ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℤ 0ℓ
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel ℤ 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel ℤ 0ℓ
x ≯ y = ¬ (x > y)

------------------------------------------------------------------------
-- Conversions

-- Absolute value.

∣_∣ : ℤ → ℕ
∣ + n      ∣ = n
∣ -[1+ n ] ∣ = ℕ.suc n

-- Gives the sign. For zero the sign is arbitrarily chosen to be +.

sign : ℤ → Sign
sign (+ _)    = Sign.+
sign -[1+ _ ] = Sign.-

------------------------------------------------------------------------
-- A view of integers as sign + absolute value

infix 5 _◂_ _◃_

_◃_ : Sign → ℕ → ℤ
_      ◃ ℕ.zero  = + ℕ.zero
Sign.+ ◃ n       = + n
Sign.- ◃ ℕ.suc n = -[1+ n ]

data SignAbs : ℤ → Set where
  _◂_ : (s : Sign) (n : ℕ) → SignAbs (s ◃ n)

signAbs : ∀ i → SignAbs i
signAbs -[1+ n ] = Sign.- ◂ ℕ.suc n
signAbs +0       = Sign.+ ◂ ℕ.zero
signAbs +[1+ n ] = Sign.+ ◂ ℕ.suc n

------------------------------------------------------------------------
-- Arithmetic

-- Negation.

-_ : ℤ → ℤ
- -[1+ n ] = +[1+ n ]
- +0       = +0
- +[1+ n ] = -[1+ n ]

-- Subtraction of natural numbers.

_⊖_ : ℕ → ℕ → ℤ
m       ⊖ ℕ.zero  = + m
ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
ℕ.suc m ⊖ ℕ.suc n = m ⊖ n

-- Addition.

_+_ : ℤ → ℤ → ℤ
-[1+ m ] + -[1+ n ] = -[1+ ℕ.suc (m ℕ+ n) ]
-[1+ m ] + +    n   = n ⊖ ℕ.suc m
+    m   + -[1+ n ] = m ⊖ ℕ.suc n
+    m   + +    n   = + (m ℕ+ n)

-- Subtraction.

_-_ : ℤ → ℤ → ℤ
i - j = i + (- j)

-- Successor.

suc : ℤ → ℤ
suc i = (+ 1) + i

-- Predecessor.

pred : ℤ → ℤ
pred i = (- + 1) + i

-- Multiplication.

_*_ : ℤ → ℤ → ℤ
i * j = sign i S* sign j ◃ ∣ i ∣ ℕ* ∣ j ∣

-- Maximum.

_⊔_ : ℤ → ℤ → ℤ
-[1+ m ] ⊔ -[1+ n ] = -[1+ ℕ._⊓_ m n ]
-[1+ m ] ⊔ +    n   = + n
+    m   ⊔ -[1+ n ] = + m
+    m   ⊔ +    n   = + (ℕ._⊔_ m n)

-- Minimum.

_⊓_ : ℤ → ℤ → ℤ
-[1+ m ] ⊓ -[1+ n ] = -[1+ ℕ._⊔_ m n ]
-[1+ m ] ⊓ +    n   = -[1+ m ]
+    m   ⊓ -[1+ n ] = -[1+ n ]
+    m   ⊓ +    n   = + (ℕ._⊓_ m n)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

-- The following definition of _<_ results in the unsolved metas for the
-- first argument in certain situations.

infix  4 _<′_ _>′_ _≮′_ _≯′_

_<′_ : Rel ℤ _
x <′ y = suc x ≤ y
{-# WARNING_ON_USAGE _<′_
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
_>′_ : Rel ℤ _
x >′ y = y <′ x
{-# WARNING_ON_USAGE _>′_
"Warning: _>′_ was deprecated in v1.1.
Please use _>_ instead."
#-}
_≮′_ : Rel ℤ _
x ≮′ y = ¬ (x <′ y)
{-# WARNING_ON_USAGE _≮′_
"Warning: _≮′_ was deprecated in v1.1.
Please use _≮_ instead."
#-}
_≯′_ : Rel ℤ _
x ≯′ y = ¬ (x >′ y)
{-# WARNING_ON_USAGE _≯′_
"Warning: _≯′_ was deprecated in v1.1.
Please use _≯_ instead."
#-}

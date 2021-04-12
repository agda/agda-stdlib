------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers, basic types and operations
------------------------------------------------------------------------

-- See README.Data.Integer for examples of how to use and reason about
-- integers.

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

module Data.Integer.Base where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base as ℕ
  using (ℕ; z≤n; s≤s) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Sign as Sign using (Sign) renaming (_*_ to _S*_)
open import Function
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

infix  8 -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊖_ _⊔_
infix  4 _≤_ _≥_ _<_ _>_ _≰_ _≱_ _≮_ _≯_
infix  4 _≤ᵇ_

------------------------------------------------------------------------
-- Types

open import Agda.Builtin.Int public
  using ()
  renaming
  ( Int    to ℤ
  ; pos    to +_      -- "+ n"      stands for "n"
  ; negsuc to -[1+_]  -- "-[1+ n ]" stands for "- (1 + n)"
  )

-- Some additional patterns that provide symmetry around 0

pattern +0       = + 0
pattern +[1+_] n = + (ℕ.suc n)

------------------------------------------------------------------------
-- Constants

0ℤ : ℤ
0ℤ = +0

-1ℤ : ℤ
-1ℤ = -[1+ 0 ]

1ℤ : ℤ
1ℤ = +[1+ 0 ]

------------------------------------------------------------------------
-- Conversion

-- Absolute value.

∣_∣ : ℤ → ℕ
∣ + n      ∣ = n
∣ -[1+ n ] ∣ = ℕ.suc n

-- Gives the sign. For zero the sign is arbitrarily chosen to be +.

sign : ℤ → Sign
sign (+ _)    = Sign.+
sign -[1+ _ ] = Sign.-

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
-- Boolean ordering

-- A boolean version.
_≤ᵇ_ : ℤ → ℤ → Bool
-[1+ m ] ≤ᵇ -[1+ n ] = n ℕ.≤ᵇ m
(+ m)    ≤ᵇ -[1+ n ] = false
-[1+ m ] ≤ᵇ (+ n)    = true
(+ m)    ≤ᵇ (+ n)    = m ℕ.≤ᵇ n

------------------------------------------------------------------------
-- Simple predicates

-- See `Data.Nat.Base` for a discussion on the design of these.

NonZero : Pred ℤ 0ℓ
NonZero i = ℕ.NonZero ∣ i ∣

Positive : Pred ℤ 0ℓ
Positive +[1+ n ] = ⊤
Positive +0       = ⊥
Positive -[1+ n ] = ⊥

Negative : Pred ℤ 0ℓ
Negative (+ n)    = ⊥
Negative -[1+ n ] = ⊤

NonPositive : Pred ℤ 0ℓ
NonPositive +[1+ n ] = ⊥
NonPositive +0       = ⊤
NonPositive -[1+ n ] = ⊤

NonNegative : Pred ℤ 0ℓ
NonNegative (+ n)    = ⊤
NonNegative -[1+ n ] = ⊥

-- Constructors

≢-nonZero : ∀ {i} → i ≢ 0ℤ → NonZero i
≢-nonZero { +[1+ n ]} _   = _
≢-nonZero { +0}       0≢0 = 0≢0 refl
≢-nonZero { -[1+ n ]} _   = _

>-nonZero : ∀ {i} → i > 0ℤ → NonZero i
>-nonZero (+<+ (s≤s m<n)) = _

<-nonZero : ∀ {i} → i < 0ℤ → NonZero i
<-nonZero -<+ = _

positive : ∀ {i} → i > 0ℤ → Positive i
positive (+<+ (s≤s m<n)) = _

negative : ∀ {i} → i < 0ℤ → Negative i
negative -<+ = _

nonPositive : ∀ {i} → i ≤ 0ℤ → NonPositive i
nonPositive -≤+       = _
nonPositive (+≤+ z≤n) = _

nonNegative : ∀ {i} → i ≥ 0ℤ → NonNegative i
nonNegative {+0}       _ = _
nonNegative {+[1+ n ]} _ = _

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
-- We define it using _<ᵇ_ and _∸_ rather than inductively so that it
-- is backed by builtin operations. This makes it much faster.
_⊖_ : ℕ → ℕ → ℤ
m ⊖ n with m ℕ.<ᵇ n
... | true  = - + (n ℕ.∸ m)
... | false = + (m ℕ.∸ n)

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
suc i = 1ℤ + i

-- Predecessor.

pred : ℤ → ℤ
pred i = -1ℤ + i

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

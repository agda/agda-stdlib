------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers, basic types and operations
------------------------------------------------------------------------

-- See README.Data.Integer for examples of how to use and reason about
-- integers.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Base where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawGroup; RawNearSemiring; RawSemiring; RawRing)
open import Data.Bool.Base using (Bool; T; true; false)
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
open import Data.Sign.Base as Sign using (Sign)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Unary using (Pred)

infix  8 -_
infixr 8 _^_
infixl 7 _*_ _⊓_ _/ℕ_ _/_ _%ℕ_ _%_
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

record Positive (i : ℤ) : Set where
  field
    pos : T (1ℤ ≤ᵇ i)

record NonNegative (i : ℤ) : Set where
  field
    nonNeg : T (0ℤ ≤ᵇ i)

record NonPositive (i : ℤ) : Set where
  field
    nonPos : T (i ≤ᵇ 0ℤ)

record Negative (i : ℤ) : Set where
  field
    neg : T (i ≤ᵇ -1ℤ)

-- Instances

instance
  pos : ∀ {n} → Positive +[1+ n ]
  pos = _

  nonNeg : ∀ {n} → NonNegative (+ n)
  nonNeg = _

  nonPos0 : NonPositive 0ℤ
  nonPos0 = _

  nonPos : ∀ {n} → NonPositive -[1+ n ]
  nonPos = _

  neg : ∀ {n} → Negative -[1+ n ]
  neg = _

-- Constructors

≢-nonZero : ∀ {i} → i ≢ 0ℤ → NonZero i
≢-nonZero { +[1+ n ]} _   = _
≢-nonZero { +0}       0≢0 = contradiction refl 0≢0
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
_      ◃ ℕ.zero  = +0
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
-[1+ m ] + -[1+ n ] = -[1+ ℕ.suc (m ℕ.+ n) ]
-[1+ m ] + +    n   = n ⊖ ℕ.suc m
+    m   + -[1+ n ] = m ⊖ ℕ.suc n
+    m   + +    n   = + (m ℕ.+ n)

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
i * j = sign i Sign.* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣

-- Naïve exponentiation.

_^_ : ℤ → ℕ → ℤ
i ^ ℕ.zero    = 1ℤ
i ^ (ℕ.suc m) = i * i ^ m

-- Maximum.

_⊔_ : ℤ → ℤ → ℤ
-[1+ m ] ⊔ -[1+ n ] = -[1+ ℕ._⊓_ m n ]
-[1+ m ] ⊔ +    n   = + n
+    m   ⊔ -[1+ n ] = + m
+    m   ⊔ +    n   = + (ℕ._⊔_ m n)

-- Minimum.

_⊓_ : ℤ → ℤ → ℤ
-[1+ m ] ⊓ -[1+ n ] = -[1+ m ℕ.⊔ n ]
-[1+ m ] ⊓ +    n   = -[1+ m ]
+    m   ⊓ -[1+ n ] = -[1+ n ]
+    m   ⊓ +    n   = + (m ℕ.⊓ n)

-- Division by a natural

_/ℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℤ
(+ n      /ℕ d) = + (n ℕ./ d)
(-[1+ n ] /ℕ d) with ℕ.suc n ℕ.% d
... | ℕ.zero  = - (+ (ℕ.suc n ℕ./ d))
... | ℕ.suc r = -[1+ (ℕ.suc n ℕ./ d) ]

-- Division

_/_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℤ
i / j = (sign j ◃ 1) * (i /ℕ ∣ j ∣)

-- Modulus by a natural

_%ℕ_ : (dividend : ℤ) (divisor : ℕ) .{{_ : ℕ.NonZero divisor}} → ℕ
(+ n      %ℕ d) = n ℕ.% d
(-[1+ n ] %ℕ d) with ℕ.suc n ℕ.% d
... | ℕ.zero      = 0
... | r@(ℕ.suc _) = d ℕ.∸ r

-- Modulus

_%_ : (dividend divisor : ℤ) .{{_ : NonZero divisor}} → ℕ
i % j = i %ℕ ∣ j ∣

------------------------------------------------------------------------
-- Bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record { _≈_ = _≡_ ; _∙_ = _+_ }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _+_ ; ε = 0ℤ }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record { _≈_ = _≡_ ; _∙_ = _+_ ; _⁻¹ = -_; ε = 0ℤ }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record { _≈_ = _≡_ ; _∙_ = _*_ }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _*_ ; ε = 1ℤ }

+-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
+-*-rawNearSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0ℤ
  }

+-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0ℤ
  ; 1# = 1ℤ
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0ℤ
  ; 1# = 1ℤ
  }


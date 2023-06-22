------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers, basic types and operations
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use and reason about
-- naturals.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Base where

open import Algebra.Bundles.Raw using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.Parity.Base using (Parity; 0ℙ; 1ℙ)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

------------------------------------------------------------------------
-- Types

open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)

------------------------------------------------------------------------
-- Boolean equality relation

open import Agda.Builtin.Nat public
  using () renaming (_==_ to _≡ᵇ_)

------------------------------------------------------------------------
-- Boolean ordering relation

open import Agda.Builtin.Nat public
  using () renaming (_<_ to _<ᵇ_)

infix 4 _≤ᵇ_
_≤ᵇ_ : (m n : ℕ) → Bool
zero  ≤ᵇ n = true
suc m ≤ᵇ n = m <ᵇ n

------------------------------------------------------------------------
-- Standard ordering relations

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

data _≤_ : Rel ℕ 0ℓ where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Rel ℕ 0ℓ
m < n = suc m ≤ n

-- Smart constructors of _<_

pattern z<s {n}         = s≤s (z≤n {n})
pattern s<s {m} {n} m<n = s≤s {m} {n} m<n

------------------------------------------------------------------------
-- other ordering relations

_≥_ : Rel ℕ 0ℓ
m ≥ n = n ≤ m

_>_ : Rel ℕ 0ℓ
m > n = n < m

_≰_ : Rel ℕ 0ℓ
a ≰ b = ¬ a ≤ b

_≮_ : Rel ℕ 0ℓ
a ≮ b = ¬ a < b

_≱_ : Rel ℕ 0ℓ
a ≱ b = ¬ a ≥ b

_≯_ : Rel ℕ 0ℓ
a ≯ b = ¬ a > b

------------------------------------------------------------------------
-- Simple predicates

-- Defining `NonZero` in terms of `T` and therefore ultimately `⊤` and
-- `⊥` allows Agda to automatically infer nonZero-ness for any natural
-- of the form `suc n`. Consequently in many circumstances this
-- eliminates the need to explicitly pass a proof when the NonZero
-- argument is either an implicit or an instance argument.
--
-- See `Data.Nat.DivMod` for an example.

record NonZero (n : ℕ) : Set where
  field
    nonZero : T (not (n ≡ᵇ 0))

-- Instances

instance
  nonZero : ∀ {n} → NonZero (suc n)
  nonZero = _

-- Constructors

≢-nonZero : ∀ {n} → n ≢ 0 → NonZero n
≢-nonZero {zero}  0≢0 = contradiction refl 0≢0
≢-nonZero {suc n} n≢0 = _

>-nonZero : ∀ {n} → n > 0 → NonZero n
>-nonZero z<s = _

-- Destructors

≢-nonZero⁻¹ : ∀ n → .{{NonZero n}} → n ≢ 0
≢-nonZero⁻¹ (suc n) ()

>-nonZero⁻¹ : ∀ n → .{{NonZero n}} → n > 0
>-nonZero⁻¹ (suc n) = z<s

------------------------------------------------------------------------
-- Arithmetic

open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)

open import Agda.Builtin.Nat
  using (div-helper; mod-helper)

pred : ℕ → ℕ
pred n = n ∸ 1

infix  8 _!
infixl 7 _⊓_ _⊓′_ _/_ _%_
infixl 6 _+⋎_ _⊔_ _⊔′_

-- Argument-swapping addition. Used by Data.Vec._⋎_.

_+⋎_ : ℕ → ℕ → ℕ
zero  +⋎ n = n
suc m +⋎ n = suc (n +⋎ m)

-- Max.

_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Max defined in terms of primitive operations.
-- This is much faster than `_⊔_` but harder to reason about. For proofs
-- involving this function, convert it to `_⊔_` with `Data.Nat.Properties.⊔≡⊔‵`.
_⊔′_ : ℕ → ℕ → ℕ
m ⊔′ n with m <ᵇ n
... | false = m
... | true  = n

-- Min.

_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

-- Min defined in terms of primitive operations.
-- This is much faster than `_⊓_` but harder to reason about. For proofs
-- involving this function, convert it to `_⊓_` wtih `Data.Nat.properties.⊓≡⊓′`.
_⊓′_ : ℕ → ℕ → ℕ
m ⊓′ n with m <ᵇ n
... | false = n
... | true  = m

-- Parity

parity : ℕ → Parity
parity 0             = 0ℙ
parity 1             = 1ℙ
parity (suc (suc n)) = parity n

-- Division by 2, rounded downwards.

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋           = 0
⌊ 1 /2⌋           = 0
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- Division by 2, rounded upwards.

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = ⌊ suc n /2⌋

-- Naïve exponentiation

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n

-- Distance

∣_-_∣ : ℕ → ℕ → ℕ
∣ zero  - y     ∣ = y
∣ x     - zero  ∣ = x
∣ suc x - suc y ∣ = ∣ x - y ∣

-- Distance in terms of primitive operations.
-- This is much faster than `∣_-_∣` but harder to reason about. For proofs
-- involving this function, convert it to `∣_-_∣` with
-- `Data.Nat.Properties.∣-∣≡∣-∣′`.
∣_-_∣′ : ℕ → ℕ → ℕ
∣ x - y ∣′ with x <ᵇ y
... | false = x ∸ y
... | true  = y ∸ x

-- Division
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_/_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
m / (suc n) = div-helper 0 n m n

-- Remainder/modulus
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_%_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
m % (suc n) = mod-helper 0 n m n

-- Factorial

_! : ℕ → ℕ
zero  ! = 1
suc n ! = suc n * n !

------------------------------------------------------------------------
-- Alternative definition of _≤_

-- The following definition of _≤_ is more suitable for well-founded
-- induction (see Data.Nat.Induction)

infix 4 _≤′_ _<′_ _≥′_ _>′_

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

_<′_ : Rel ℕ 0ℓ
m <′ n = suc m ≤′ n

-- Smart constructors of _<′_

pattern <′-base          = ≤′-refl
pattern <′-step {n} m<′n = ≤′-step {n} m<′n

_≥′_ : Rel ℕ 0ℓ
m ≥′ n = n ≤′ m

_>′_ : Rel ℕ 0ℓ
m >′ n = n <′ m

------------------------------------------------------------------------
-- Another alternative definition of _≤_

record _≤″_ (m n : ℕ) : Set where
  constructor less-than-or-equal
  field
    {k}   : ℕ
    proof : m + k ≡ n

infix 4 _≤″_ _<″_ _≥″_ _>″_

_<″_ : Rel ℕ 0ℓ
m <″ n = suc m ≤″ n

_≥″_ : Rel ℕ 0ℓ
m ≥″ n = n ≤″ m

_>″_ : Rel ℕ 0ℓ
m >″ n = n <″ m

------------------------------------------------------------------------
-- Another alternative definition of _≤_

-- Useful for induction when you have an upper bound.

data _≤‴_ : ℕ → ℕ → Set where
  ≤‴-refl : ∀{m} → m ≤‴ m
  ≤‴-step : ∀{m n} → suc m ≤‴ n → m ≤‴ n

infix 4 _≤‴_ _<‴_ _≥‴_ _>‴_

_<‴_ : Rel ℕ 0ℓ
m <‴ n = suc m ≤‴ n

_≥‴_ : Rel ℕ 0ℓ
m ≥‴ n = n ≤‴ m

_>‴_ : Rel ℕ 0ℓ
m >‴ n = n <‴ m

------------------------------------------------------------------------
-- A comparison view. Taken from "View from the left"
-- (McBride/McKinna); details may differ.

data Ordering : Rel ℕ 0ℓ where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
... | less    m k = less (suc m) k
... | equal   m   = equal (suc m)
... | greater n k = greater (suc n) k

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0
  }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε = 1
  }

+-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
+-*-rawNearSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  }

+-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  }


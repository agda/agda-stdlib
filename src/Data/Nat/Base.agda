------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers, basic types and operations
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use and reason about
-- naturals.

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Base where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred)

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

-- Defining `NonZero` in terms of `⊤` and `⊥` allows Agda to
-- automatically infer nonZero-ness for any natural of the form
-- `suc n`. Consequently in many circumstances this eliminates the need
-- to explicitly pass a proof when the NonZero argument is either an
-- implicit or an instance argument.
--
-- It could alternatively be defined using a datatype with an instance
-- constructor but then it would not be inferrable when passed as an
-- implicit argument.
--
-- See `Data.Nat.DivMod` for an example.

NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc x) = ⊤

-- Constructors

≢-nonZero : ∀ {n} → n ≢ 0 → NonZero n
≢-nonZero {zero}  0≢0 = 0≢0 refl
≢-nonZero {suc n} n≢0 = tt

>-nonZero : ∀ {n} → n > 0 → NonZero n
>-nonZero (s≤s 0<n) = tt

------------------------------------------------------------------------
-- Arithmetic

open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)

pred : ℕ → ℕ
pred n = n ∸ 1

infixl 7 _⊓_
infixl 6 _+⋎_ _⊔_

-- Argument-swapping addition. Used by Data.Vec._⋎_.

_+⋎_ : ℕ → ℕ → ℕ
zero  +⋎ n = n
suc m +⋎ n = suc (n +⋎ m)

-- Max.

_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Min.

_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

-- Division by 2, rounded downwards.

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋           = 0
⌊ 1 /2⌋           = 0
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- Division by 2, rounded upwards.

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = ⌊ suc n /2⌋

-- Naïve exponentiation

_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n

-- Distance

∣_-_∣ : ℕ → ℕ → ℕ
∣ zero  - y     ∣ = y
∣ x     - zero  ∣ = x
∣ suc x - suc y ∣ = ∣ x - y ∣

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

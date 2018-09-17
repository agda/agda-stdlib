------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers, basic types and operations
------------------------------------------------------------------------

module Data.Nat.Base where

open import Level using (0ℓ)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core

open import Relation.Nullary using (¬_; Dec; yes; no)

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

------------------------------------------------------------------------
-- The types

open import Agda.Builtin.Nat public
  using    ( zero; suc; _+_; _*_ )
  renaming ( Nat to ℕ
           ; _-_ to _∸_ )

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

-- The following, alternative definition of _≤_ is more suitable for
-- well-founded induction (see Induction.Nat).

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

-- Another alternative definition of _≤_.

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
-- Arithmetic

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

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

------------------------------------------------------------------------
-- Queries

infix 4 _≟_ _≤?_

_≟_ : Decidable {A = ℕ} _≡_
zero  ≟ zero   = yes refl
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()
suc m ≟ suc n  with m ≟ n
... | yes refl = yes refl
... | no m≢n   = no (m≢n ∘ (λ p → subst (λ x → m ≡ pred x) p refl))

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

_≤?_ : Decidable _≤_
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no λ()
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no  m≰n = no  (m≰n ∘ ≤-pred)

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

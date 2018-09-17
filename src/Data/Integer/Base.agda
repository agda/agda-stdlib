------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers, basic types and operations
------------------------------------------------------------------------

module Data.Integer.Base where

open import Data.Nat.Base as ℕ
  using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Sign as Sign using (Sign) renaming (_*_ to _S*_)
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix  8 -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊖_ _⊔_
infix  4 _≤_ _≥_ _<_ _>_ _≰_ _≱_ _≮_ _≯_

------------------------------------------------------------------------
-- The types

-- Integers.

open import Agda.Builtin.Int public
  using ()
  renaming ( Int to ℤ
           ; negsuc to -[1+_]  -- -[1+ n ] stands for - (1 + n).
           ; pos    to +_ )    -- + n stands for n.

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

◃-left-inverse : ∀ i → sign i ◃ ∣ i ∣ ≡ i
◃-left-inverse -[1+ n ]    = refl
◃-left-inverse (+ ℕ.zero)  = refl
◃-left-inverse (+ ℕ.suc n) = refl

data SignAbs : ℤ → Set where
  _◂_ : (s : Sign) (n : ℕ) → SignAbs (s ◃ n)

------------------------------------------------------------------------
-- Arithmetic

-- Negation.

-_ : ℤ → ℤ
- (+ ℕ.suc n) = -[1+ n ]
- (+ ℕ.zero)  = + ℕ.zero
- -[1+ n ]    = + ℕ.suc n

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
i - j = i + - j

-- Successor.

suc : ℤ → ℤ
suc i = + 1 + i

private

  suc-is-lazy⁺ : ∀ n → suc (+ n) ≡ + ℕ.suc n
  suc-is-lazy⁺ n = refl

  suc-is-lazy⁻ : ∀ n → suc -[1+ ℕ.suc n ] ≡ -[1+ n ]
  suc-is-lazy⁻ n = refl

-- Predecessor.

pred : ℤ → ℤ
pred i = - + 1 + i

private

  pred-is-lazy⁺ : ∀ n → pred (+ ℕ.suc n) ≡ + n
  pred-is-lazy⁺ n = refl

  pred-is-lazy⁻ : ∀ n → pred -[1+ n ] ≡ -[1+ ℕ.suc n ]
  pred-is-lazy⁻ n = refl

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
-- Ordering

data _≤_ : ℤ → ℤ → Set where
  -≤+ : ∀ {m n} → -[1+ m ] ≤ + n
  -≤- : ∀ {m n} → (n≤m : n ℕ.≤ m) → -[1+ m ] ≤ -[1+ n ]
  +≤+ : ∀ {m n} → (m≤n : m ℕ.≤ n) → + m ≤ + n

_≥_ : Rel ℤ _
x ≥ y = y ≤ x

_<_ : Rel ℤ _
x < y = suc x ≤ y

_>_ : Rel ℤ _
x > y = y < x

_≰_ : Rel ℤ _
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℤ _
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel ℤ _
x ≮ y = ¬ (x < y)

_≯_ : Rel ℤ _
x ≯ y = ¬ (x > y)

drop‿+≤+ : ∀ {m n} → + m ≤ + n → ℕ._≤_ m n
drop‿+≤+ (+≤+ m≤n) = m≤n

drop‿-≤- : ∀ {m n} → -[1+ m ] ≤ -[1+ n ] → ℕ._≤_ n m
drop‿-≤- (-≤- n≤m) = n≤m

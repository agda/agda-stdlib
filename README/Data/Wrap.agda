------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how to use `Wrap` to help term inference.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Wrap where

open import Data.Wrap

open import Algebra
open import Data.Product
open import Level using (Level)

private
  variable
    c ℓ : Level

-- `Monoid.Carrier` gets the carrier set from a monoid, and thus has
-- type `Monoid c ℓ → Set c`.
-- Using `Wrap`, we can convert `Monoid.Carrier` into an equivalent
-- “wrapped” version: `MonoidEl`.
MonoidEl : Monoid c ℓ → Set c
MonoidEl = Wrap Monoid.Carrier

-- We can turn any monoid into the equivalent monoid where the elements
-- and equations have been wrapped.
-- The translation mainly consists of wrapping and unwrapping everything
-- via the `Wrap` constructor, `mk`.
-- Notice that the equality field is wrapping the binary relation
-- `_≈_ : (x y : Carrier) → Set ℓ`, giving an example of how `Wrap` works
-- for arbitrary n-ary relations.
Wrap-monoid : Monoid c ℓ → Monoid c ℓ
Wrap-monoid M = record
  { Carrier = MonoidEl M
  ; _≈_ = λ (mk x) (mk y) → Wrap _≈_ x y
  ; _∙_ = λ (mk x) (mk y) → mk (x ∙ y)
  ; ε = mk ε
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl = mk refl
          ; sym = λ (mk xy) → mk (sym xy)
          ; trans = λ (mk xy) (mk yz) → mk (trans xy yz)
          }
        ; ∙-cong = λ (mk xx) (mk yy) → mk (∙-cong xx yy)
        }
      ; assoc = λ (mk x) (mk y) (mk z) → mk (assoc x y z)
      }
    ; identity = (λ (mk x) → mk (identityˡ x))
               , (λ (mk x) → mk (identityʳ x))
    }
  }
  where open Monoid M

-- Usually, we would only open one monoid at a time.
-- If we were to open two monoids `M` and `N` simultaneously, Agda would
-- get confused whenever it came across, for example, `_∙_`, not knowing
-- whether it came from `M` or `N`.
-- This is true whether or not `M` and `N` can be disambiguated by some
-- other means (such as by their `Carrier`s).

-- However, with wrapped monoids, we are going to remember the monoid
-- while checking any monoid expressions, so we can afford to have just
-- one, polymorphic, version of `_∙_` visible globally.
open module Wrap-monoid {c ℓ} {M : Monoid c ℓ} = Monoid (Wrap-monoid M)

-- Now we can test out this construct on some existing monoids.

open import Data.Nat
open import Data.Nat.Properties

-- Notice that, while the following two definitions appear to be defined
-- by the same expression, their types are genuinely different.
-- Whereas `Carrier +-0-monoid = ℕ = Carrier *-1-monoid`, `MonoidEl M`
-- does not compute, and thus
-- `MonoidEl +-0-monoid ≠ MonoidEl *-1-monoid` definitionally.
-- This lets us use the respective monoids when checking the respective
-- definitions.

test-+ : MonoidEl +-0-monoid
test-+ = (mk 3 ∙ ε) ∙ mk 2

test-* : MonoidEl *-1-monoid
test-* = (mk 3 ∙ ε) ∙ mk 2

-- The reader is invited to normalise these two definitions
-- (`C-c C-n`, then type in the name).
-- `test-+` is interpreted using (ℕ, +, 0), and thus computes to `mk 5`.
-- Meanwhile, `test-*` is interpreted using (ℕ, *, 1), and thus computes
-- to `mk 6`.

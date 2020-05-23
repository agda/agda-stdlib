------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how to use `Wrap` to help term inference.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Wrap where

open import Data.Wrap

open import Algebra
open import Data.Nat
open import Data.Product
open import Level using (Level)
open import Relation.Binary

private
  variable
    c ℓ : Level
    A : Set c
    m n : ℕ

------------------------------------------------------------------------
-- `Wrap` for remembering instances
------------------------------------------------------------------------

module Instances where

  -- `Monoid.Carrier` gets the carrier set from a monoid, and thus has
  -- type `Monoid c ℓ → Set c`.
  -- Using `Wrap`, we can convert `Monoid.Carrier` into an equivalent
  -- “wrapped” version: `MonoidEl`.
  MonoidEl : Monoid c ℓ → Set c
  MonoidEl = Wrap Monoid.Carrier

  -- We can turn any monoid into the equivalent monoid where the elements
  -- and equations have been wrapped.
  -- The translation mainly consists of wrapping and unwrapping everything
  -- via the `Wrap` constructor, `[_]`.
  -- Notice that the equality field is wrapping the binary relation
  -- `_≈_ : (x y : Carrier) → Set ℓ`, giving an example of how `Wrap` works
  -- for arbitrary n-ary relations.
  Wrap-monoid : Monoid c ℓ → Monoid c ℓ
  Wrap-monoid M = record
    { Carrier = MonoidEl M
    ; _≈_ = λ ([ x ]) ([ y ]) → Wrap _≈_ x y
    ; _∙_ = λ ([ x ]) ([ y ]) → [ x ∙ y ]
    ; ε = [ ε ]
    ; isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl = [ refl ]
            ; sym = λ ([ xy ]) → [ sym xy ]
            ; trans = λ ([ xy ]) ([ yz ]) → [ trans xy yz ]
            }
          ; ∙-cong = λ ([ xx ]) ([ yy ]) → [ ∙-cong xx yy ]
          }
        ; assoc = λ ([ x ]) ([ y ]) ([ z ]) → [ assoc x y z ]
        }
      ; identity = (λ ([ x ]) → [ identityˡ x ])
                 , (λ ([ x ]) → [ identityʳ x ])
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

  open import Data.Nat.Properties

  -- Notice that, while the following two definitions appear to be defined
  -- by the same expression, their types are genuinely different.
  -- Whereas `Carrier +-0-monoid = ℕ = Carrier *-1-monoid`, `MonoidEl M`
  -- does not compute, and thus
  -- `MonoidEl +-0-monoid ≠ MonoidEl *-1-monoid` definitionally.
  -- This lets us use the respective monoids when checking the respective
  -- definitions.

  test-+ : MonoidEl +-0-monoid
  test-+ = ([ 3 ] ∙ ε) ∙ [ 2 ]

  test-* : MonoidEl *-1-monoid
  test-* = ([ 3 ] ∙ ε) ∙ [ 2 ]

  -- The reader is invited to normalise these two definitions
  -- (`C-c C-n`, then type in the name).
  -- `test-+` is interpreted using (ℕ, +, 0), and thus computes to `[ 5 ]`.
  -- Meanwhile, `test-*` is interpreted using (ℕ, *, 1), and thus computes
  -- to `[ 6 ]`.

------------------------------------------------------------------------
-- `Wrap` for dealing with dependent functions
------------------------------------------------------------------------

module Dependent′ (monoid : Monoid c ℓ) where
  open Monoid monoid

  open import Data.Fin
  open import Data.Vec.Functional

  infix 4 _≈ᵥ_
  infixl 7 _∙ᵥ_

  _≈ᵥ_ : (u v : Vector Carrier n) → Set _
  u ≈ᵥ v = ∀ i → u i ≈ v i

  transᵥ : Transitive (_≈ᵥ_ {n = n})
  transᵥ uv vw i = trans (uv i) (vw i)

  εᵥ : Vector Carrier n
  εᵥ i = ε

  _∙ᵥ_ : (u v : Vector Carrier n) → Vector Carrier n
  (u ∙ᵥ v) i = u i ∙ v i

  assocᵥ : (u v w : Vector Carrier n) → (u ∙ᵥ v) ∙ᵥ w ≈ᵥ u ∙ᵥ (v ∙ᵥ w)
  assocᵥ u v w i = assoc (u i) (v i) (w i)

  lemma : (t u v w : Vector Carrier n) →
          ((t ∙ᵥ u) ∙ᵥ v) ∙ᵥ w ≈ᵥ t ∙ᵥ (u ∙ᵥ (v ∙ᵥ w))
  lemma t u v w = transᵥ (assocᵥ _ _ _) (assocᵥ _ _ _)

module Dependent {A : Set c} (_≈_ : Rel A ℓ) where

  open import Data.Fin
  open import Data.Vec.Functional

  _≈ᵥ_ : (u v : Vector A n) → Set _
  u ≈ᵥ v = ∀ i → u i ≈ v i

  symᵥ : Symmetric _≈_ → Symmetric (_≈ᵥ_ {n = n})
  symᵥ sym uv i = sym (uv i)

  transᵥ : Transitive _≈_ → Transitive (_≈ᵥ_ {n = n})
  transᵥ trans uv vw i = trans (uv i) (vw i)

  reindex : (Fin m → Fin n) → Vector A n → Vector A m
  reindex f v i = v (f i)

  reindex-cong : ∀ (f : Fin m → Fin n) {u v} →
                 u ≈ᵥ v → reindex f u ≈ᵥ reindex f v
  reindex-cong f uv i = uv (f i)

  lemma : ∀ (f : Fin m → Fin n) {u v} →
          u ≈ᵥ v → reindex f u ≈ᵥ reindex f v
  lemma f uv = reindex-cong _ uv

  module WithMonoid (monoid : Monoid c ℓ) where
    open Monoid monoid

    εᵥ : Vector Carrier n
    εᵥ i = ε

    _∙ᵥ_ : (u v : Vector Carrier n) → Vector Carrier n
    (u ∙ᵥ v) i = u i ∙ v i

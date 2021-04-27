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
open import Data.Nat.Properties
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
-- `Wrap` for dealing with functions spoiling unification
------------------------------------------------------------------------

module Unification where

  open import Relation.Binary.PropositionalEquality

  module Naïve where

    -- We want to work with factorisations of natural numbers in a
    -- “proof-relevant” style. We could draw out `Factor m n o` as
    --   m
    --  /*\
    -- n   o.

    Factor : (m n o : ℕ) → Set
    Factor m n o = m ≡ n * o

    -- We can prove a basic lemma about `Factor`: the following tree rotation
    -- can be done, due to associativity of `_*_`.
    --      m             m
    --     /*\           /*\
    --   no   p  ---->  n   op
    --  /*\                 /*\
    -- n   o               o   p

    assoc-→ : ∀ {m n o p} →
              (∃ λ no → Factor m no p × Factor no n o) →
              (∃ λ op → Factor m n op × Factor op o p)
    assoc-→ {m} {n} {o} {p} (._ , refl , refl) = _ , *-assoc n o p , refl

    -- We must give at least some arguments to `*-assoc`, as Agda is unable to
    -- unify `? * ? * ?` with `n * o * p`, as `_*_` is a function and not
    -- necessarily injective (and indeed not injective when one of its
    -- arguments is 0).

    -- We now want to use this lemma in a more complex proof:
    --         m            m
    --        /*\          /*\
    --     nop   q        n   opq
    --     /*\      ---->     /*\
    --   no   p              o   pq
    --  /*\                      /*\
    -- n   o                    p   q

    test : ∀ {m n o p q} →
           (∃₂ λ no nop → Factor m nop q × Factor nop no p × Factor no n o) →
           (∃₂ λ pq opq → Factor m n opq × Factor opq o pq × Factor pq p q)
    test {n = n} (no , nop , fm , fnop , fno) =
      let _ , fm , fpq = assoc-→ {n = no} (_ , fm , fnop) in
      let _ , fm , fopq = assoc-→ {n = n} (_ , fm , fno) in
      _ , _ , fm , fopq , fpq

    -- This works okay, but where we have written `{n = no}` and similar, we
    -- are being forced to deal with details we don't really care about. Agda
    -- should be able to fill in the vertices given part of a tree, but can't
    -- due to similar reasons as before: `Factor ? ? ?` doesn't unify against
    -- `Factor m no p`, because both instances of `Factor` compute and we're
    -- left trying to unify `? * ?` against `no * p`.

  module Wrapped where

    -- We can use `Wrap` to stop the computation of `Factor`.

    Factor : (m n o : ℕ) → Set
    Factor = Wrap λ m n o → m ≡ n * o

    -- Because `assoc-→` needs access to the implementation of `Factor`, the
    -- proof is exactly as before except for using `[_]` to wrap and unwrap.

    assoc-→ : ∀ {m n o p} →
              (∃ λ no → Factor m no p × Factor no n o) →
              (∃ λ op → Factor m n op × Factor op o p)
    assoc-→ {m} {n} {o} {p} (._ , [ refl ] , [ refl ]) =
      _ , [ *-assoc n o p ] , [ refl ]

    -- The difference is that now we have our basic lemma, the complex proof
    -- can work purely in terms of `Factor` trees. In particular,
    -- `Factor ? ? ?` now does unify with `Factor m no p`, so we don't have to
    -- give `no` explicitly again.

    test : ∀ {m n o p q} →
           (∃₂ λ no nop → Factor m nop q × Factor nop no p × Factor no n o) →
           (∃₂ λ pq opq → Factor m n opq × Factor opq o pq × Factor pq p q)
    test (_ , _ , fm , fnop , fno) =
      let _ , fm , fpq = assoc-→ (_ , fm , fnop) in
      let _ , fm , fopq = assoc-→ (_ , fm , fno) in
      _ , _ , fm , fopq , fpq

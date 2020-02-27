------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a binary one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Unary.Closure.Base {a b} {A : Set a} (R : Rel A b) where

open import Level
open import Data.Product using (Σ-syntax; _×_; _,_; -,_)
open import Function.Base using (flip)
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Definitions

-- Box

-- We start with the definition of □ ("box") which is named after the box
-- modality in modal logic. `□ T x` states that all the elements one step
-- away from `x` with respect to the relation R satisfy `T`.

□ : ∀ {t} → Pred A t → Pred A (a ⊔ b ⊔ t)
□ T x = ∀ {y} → R x y → T y

-- Use cases of □ include:
-- * The definition of the accessibility predicate corresponding to R:
--   data Acc (x : A) : Set (a ⊔ b) where
--     step : □ Acc x → Acc x

-- * The characterization of stability under weakening: picking R to be
--   `Data.List.Relation.Sublist.Inductive`, `∀ {Γ} → Tm Γ → □ T Γ`
--   corresponds to the fact that we have a notion of weakening for `Tm`.

-- Diamond

-- We then have the definition of ◇ ("diamond") which is named after the
-- diamond modality in modal logic. In modal logic, `◇ T x` states that
-- there exists an element one step away from x with respect to the
-- relation R that satisfies T. It is worth noting that the modal logic
-- metaphor breaks down here: this only is a closure operator if the step
-- we take is *backwards* with respect to R.

◇ : ∀ {t} → Pred A t → Pred A (a ⊔ b ⊔ t)
◇ T x = Σ[ support ∈ A ] (R support x × T support)

-- Use cases of ◇ include:
-- * The characterization of strengthening: picking R to be
--   `Data.List.Relation.Sublist.Inductive`, `∀ {Γ} → Tm Γ → ◇ Tm Γ`
--   is the type of a function strengthening a term to its support:
--   all the unused variables are discarded early on by the `related`
--   proof.
-- Cf. Conor McBride's "Everybody's got to be somewhere" for a more
-- detailed treatment of such an example.

-- Closed

-- Whenever we have a value in one context, we can get one in any
-- related context.

record Closed {t} (T : Pred A t) : Set (a ⊔ b ⊔ t) where
  field next : ∀ {x} → T x → □ T x


------------------------------------------------------------------------
-- Basic functions relating □ and ◇

module _ {t p} {T : Pred A t} {P : Pred A p} where

  curry : (∀ {x} → ◇ T x → P x) → (∀ {x} → T x → □ P x)
  curry f tx x∼y = f (-, x∼y , tx)

  uncurry : (∀ {x} → T x → □ P x) → (∀ {x} → ◇ T x → P x)
  uncurry f (_ , y∼x , ty) = f ty y∼x

------------------------------------------------------------------------
-- Properties

module □ {t} {T : Pred A t} where

  reindex : Transitive R → ∀ {x y} → R x y → □ T x → □ T y
  reindex trans x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

  -- Provided that R is reflexive and Transitive, □ is a comonad
  map : ∀ {u} {U : Pred A u} {x} → (∀ {x} → T x → U x) → □ T x → □ U x
  map f □Tx x~y = f (□Tx x~y)

  extract : Reflexive R → ∀ {x} → □ T x → T x
  extract refl □Tx = □Tx refl

  duplicate : Transitive R → ∀ {x} → □ T x → □ (□ T) x
  duplicate trans □Tx x∼y y∼z = □Tx (trans x∼y y∼z)

  -- Provided that R is transitive, □ is a closure operator
  -- i.e. for any `T`, `□ T` is closed.
  closed : Transitive R → Closed (□ T)
  closed trans = record { next = duplicate trans }

module ◇ {t} {T : Pred A t} where

  reindex : Transitive R → ∀ {x y} → R x y → ◇ T x → ◇ T y
  reindex trans x∼y (z , z∼x , tz) = z , trans z∼x x∼y , tz

  -- Provided that R is reflexive and Transitive, ◇ is a monad
  map : ∀ {u} {U : Pred A u} {x} → (∀ {x} → T x → U x) → ◇ T x → ◇ U x
  map f (y , y∼x , ty) = y , y∼x , f ty

  pure : Reflexive R → ∀ {x} → T x → ◇ T x
  pure refl tx = -, refl , tx

  join : Transitive R → ∀ {x} → ◇ (◇ T) x → ◇ T x
  join trans (_ , y∼x , _ , z∼y , tz) = _ , trans z∼y y∼x , tz

  -- Provided that R is transitive, ◇ is a closure operator
  -- i.e. for any `T`, `◇ T` is closed.
  closed : Transitive R → Closed (◇ T)
  closed trans = record { next = λ ◇Tx x∼y → reindex trans x∼y ◇Tx }

  run : Closed T → ∀ {x} → ◇ T x → T x
  run closed (_ , y∼x , ty) = Closed.next closed ty y∼x

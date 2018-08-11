------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a binary one.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Unary.Closure.Base {a b} {A : Set a} (R : Rel A b) where

open import Level
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Definitions

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

-- Closed: whenever we have a value in one context, we can get one in any
-- related context.

record Closed {t} (T : Pred A t) : Set (a ⊔ b ⊔ t) where
  field next : ∀ {x} → T x → □ T x


------------------------------------------------------------------------
-- Properties

module _ {t} {T : Pred A t} where

  reindex : Transitive R → ∀ {x y} → R x y → □ T x → □ T y
  reindex trans x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

  -- Provided that R is reflexive and Transitive, □ is a comonad
  map : ∀ {u} {U : Pred A u} {x} → (∀ {x} → T x → U x) → □ T x → □ U x
  map f □Tx x~y = f (□Tx x~y)

  extract : Reflexive R → ∀ {x} → □ T x → T x
  extract refl □Tx = □Tx refl

  duplicate : Transitive R → ∀ {x} → □ T x → □ (□ T) x
  duplicate trans □Tx x∼y y∼z = □Tx (trans x∼y y∼z)

-- Provided that R is transitive, □ is the Closure operator
-- i.e. for any `T`, `□ T` is closed.
□-closed : Transitive R → ∀ {t} {T : Pred A t} → Closed (□ T)
□-closed trans = record { next = duplicate trans }

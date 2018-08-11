------------------------------------------------------------------------
-- The Agda standard library
--
-- Closure of a unary relation with respect to a preorder
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Unary.Closure.Preorder {a r e} (P : Preorder a e r) where

open import Level
open import Relation.Unary using (Pred)
open Preorder P

-- We start with the definition of □ ("box") which is named after the box
-- modality in modal logic. `□ T x` states that all the elements one step
-- away from `x` with respect to the Preorder satisfy `T`.

-- Depending on whether the order is increasing or decreasing, we get either
-- the definition of the upward-closed subsets or that of the downward-closed
-- ones.
□ : ∀ {t} → Pred Carrier t → Pred Carrier (a ⊔ r ⊔ t)
□ T x = ∀ {y} → x ∼ y → T y

module _ {t} {T : Pred Carrier t} where

  reindex : ∀ {x y} → x ∼ y → □ T x → □ T y
  reindex x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

  -- □ is a comonad
  map : ∀ {u} {U : Pred Carrier u} {x} → (∀ {x} → T x → U x) → □ T x → □ U x
  map f □Tx x~y = f (□Tx x~y)

  extract : ∀ {x} → □ T x → T x
  extract □Tx = □Tx refl

  duplicate : ∀ {x} → □ T x → □ (□ T) x
  duplicate □Tx x∼y y∼z = □Tx (trans x∼y y∼z)

-- Closed: whenever we have a value in one context, we can get one in any
-- related context.
record Closed {t} (T : Pred Carrier t) : Set (a ⊔ r ⊔ t) where
  field next : ∀ {x} → T x → □ T x

-- □ is the Closure operator i.e. for any `T`, `□ T` is closed.
□-closed : ∀ {t} {T : Pred Carrier t} → Closed (□ T)
□-closed = record { next = duplicate }

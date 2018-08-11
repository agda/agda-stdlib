------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a strict partial order
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Unary.Closure.StrictPartialOrder
       {a r e} (P : StrictPartialOrder a e r) where

open import Level
open import Relation.Unary using (Pred)
open import Relation.Binary
open StrictPartialOrder P renaming (_<_ to _∼_)

-- We start with the definition of □ ("box") which is named after the box
-- modality in modal logic. `□ T x` states that all the elements one step
-- away from `x` with respect to the strict partial order satisfy `T`.

□ : ∀ {t} → Pred Carrier t → Pred Carrier (a ⊔ r ⊔ t)
□ T x = ∀ {y} → x ∼ y → T y

-- Note that this would typically be used with a decreasing order. E.g. the
-- accessibility predicate for a strict partial order R is defined as the
-- inductive type:
--
-- data Acc R x where
--   step : □ (Acc R) x → Acc R x

module _ {t} {T : Pred Carrier t} where

  map : ∀ {u} {U : Pred Carrier u} {x} → (∀ {x} → T x → U x) → □ T x → □ U x
  map f □Tx x~y = f (□Tx x~y)

  reindex : ∀ {x y} → x ∼ y → □ T x → □ T y
  reindex x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

  duplicate : ∀ {x} → □ T x → □ (□ T) x
  duplicate □Tx x∼y y∼z = □Tx (trans x∼y y∼z)

-- Closed: whenever we have a value in one context, we can get one in any
-- related context.
record Closed {t} (T : Pred Carrier t) : Set (a ⊔ r ⊔ t) where
  field next : ∀ {x} → T x → □ T x

-- □ is the Closure operator i.e. for any `T`, `□ T` is closed.
□-closed : ∀ {t} {T : Pred Carrier t} → Closed (□ T)
□-closed = record { next = duplicate }

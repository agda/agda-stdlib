------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a binary one
------------------------------------------------------------------------

module Relation.Unary.Closure where

open import Level
open import Relation.Unary using (Pred)
open import Relation.Binary as Rel hiding (module Preorder; module StrictPartialOrder)

module Preorder {a r e} (P : Preorder a e r) where
  open Rel.Preorder P

  -- Depending on whether the order is increasing or decreasing, we get either
  -- the definition of the upward-closed subsets or that of the downward-closed
  -- ones.
  □ : ∀ {t} → Pred Carrier t → Pred Carrier (a ⊔ r ⊔ t)
  □ T x = ∀ {y} → x ∼ y → T y

  module _ {t} {T : Pred Carrier t} where

    -- □ is a comonad
    map : ∀ {x y} → x ∼ y → □ T x → □ T y
    map x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

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

module StrictPartialOrder {a r e} (P : StrictPartialOrder a e r) where

  open Rel.StrictPartialOrder P renaming (_<_ to _∼_)

  □ : ∀ {t} → Pred Carrier t → Pred Carrier (a ⊔ r ⊔ t)
  □ T x = ∀ {y} → x ∼ y → T y

  -- Note that this would typically be used with a decreasing order. E.g. the
  -- accessibility predicate for a strict partial order R is defined as the
  -- inductive type:
  --
  -- data Acc R x where
  --   step : □ (Acc R) x → Acc R x

  module _ {t} {T : Pred Carrier t} where

    map : ∀ {x y} → x ∼ y → □ T x → □ T y
    map x∼y □Tx y∼z = □Tx (trans x∼y y∼z)

    duplicate : ∀ {x} → □ T x → □ (□ T) x
    duplicate □Tx x∼y y∼z = □Tx (trans x∼y y∼z)

  -- Closed: whenever we have a value in one context, we can get one in any
  -- related context.
  record Closed {t} (T : Pred Carrier t) : Set (a ⊔ r ⊔ t) where
    field next : ∀ {x} → T x → □ T x

  -- □ is the Closure operator i.e. for any `T`, `□ T` is closed.
  □-closed : ∀ {t} {T : Pred Carrier t} → Closed (□ T)
  □-closed = record { next = duplicate }

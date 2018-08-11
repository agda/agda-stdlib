------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a binary one.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Unary.Closure.Base {a b} {A : Set a} (R : Rel A b) where

open import Level
open import Relation.Unary using (Pred)

□ : ∀ {t} → Pred A t → Pred A (a ⊔ b ⊔ t)
□ T x = ∀ {y} → R x y → T y

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

-- Closed: whenever we have a value in one context, we can get one in any
-- related context.
record Closed {t} (T : Pred A t) : Set (a ⊔ b ⊔ t) where
  field next : ∀ {x} → T x → □ T x

-- □ is the Closure operator i.e. for any `T`, `□ T` is closed.
□-closed : Transitive R → ∀ {t} {T : Pred A t} → Closed (□ T)
□-closed trans = record { next = duplicate trans }

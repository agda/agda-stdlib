------------------------------------------------------------------------
-- The Agda standard library
--
-- Closure of a unary relation with respect to a preorder
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Relation.Binary

module Relation.Unary.Closure.Preorder {a r e} (P : Preorder a e r) where

open Preorder P
open import Relation.Unary using (Pred)

-- Specialising the results proven generically in `Base`.
import Relation.Unary.Closure.Base _∼_ as Base
open Base public using (□; map; Closed)

module _ {t} {T : Pred Carrier t} where

  reindex : ∀ {x y} → x ∼ y → □ T x → □ T y
  reindex = Base.reindex trans

  extract : ∀ {x} → □ T x → T x
  extract = Base.extract refl

  duplicate : ∀ {x} → □ T x → □ (□ T) x
  duplicate = Base.duplicate trans

□-closed : ∀ {t} {T : Pred Carrier t} → Closed (□ T)
□-closed = Base.□-closed trans

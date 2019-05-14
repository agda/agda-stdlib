------------------------------------------------------------------------
-- The Agda standard library
--
-- Closures of a unary relation with respect to a strict partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Unary.Closure.StrictPartialOrder
       {a r e} (P : StrictPartialOrder a e r) where

open StrictPartialOrder P renaming (_<_ to _∼_)
open import Relation.Unary using (Pred)

-- Specialising the results proven generically in `Base`.
import Relation.Unary.Closure.Base _∼_ as Base
open Base public using (□; map; Closed)

module _ {t} {T : Pred Carrier t} where

  reindex : ∀ {x y} → x ∼ y → □ T x → □ T y
  reindex = Base.reindex trans

  duplicate : ∀ {x} → □ T x → □ (□ T) x
  duplicate = Base.duplicate trans

□-closed : ∀ {t} {T : Pred Carrier t} → Closed (□ T)
□-closed = Base.□-closed trans

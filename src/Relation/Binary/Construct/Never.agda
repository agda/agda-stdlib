------------------------------------------------------------------------
-- The Agda standard library
--
-- The empty binary relation
------------------------------------------------------------------------

module Relation.Binary.Construct.Never where

open import Relation.Binary
open import Relation.Binary.Construct.Constant
open import Data.Empty using (⊥)
open import Level using (Lift; lift)

------------------------------------------------------------------------
-- Definition

Never : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Never = Const (Lift _ ⊥)

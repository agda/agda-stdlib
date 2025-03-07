------------------------------------------------------------------------
-- The Agda standard library
--
-- The empty binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Never where

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Constant using (Const)
open import Data.Empty.Polymorphic using (⊥)

------------------------------------------------------------------------
-- Definition

Never : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Never = Const ⊥

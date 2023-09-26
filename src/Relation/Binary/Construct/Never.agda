------------------------------------------------------------------------
-- The Agda standard library
--
-- The empty binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Never where

open import Relation.Binary.Core
open import Relation.Binary.Construct.Constant
open import Data.Empty.Polymorphic using (⊥)

------------------------------------------------------------------------
-- Definition

Never : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Never = Const ⊥

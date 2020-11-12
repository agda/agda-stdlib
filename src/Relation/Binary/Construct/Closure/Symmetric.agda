------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric closures of binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Symmetric where

open import Data.Sum.Base as Sum using (_⊎_)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition

SymClosure : Rel A ℓ → Rel A ℓ
SymClosure _∼_ a b = a ∼ b ⊎ b ∼ a

open Sum public using ()
  renaming (inj₁ to fwd; inj₂ to bwd)

------------------------------------------------------------------------
-- Operations

-- A generalised variant of map which allows the index type to change.
gmap : {P : Rel A ℓ₁} {Q : Rel B ℓ₂} (f : A → B) →
       P =[ f ]⇒ Q → SymClosure P =[ f ]⇒ SymClosure Q
gmap _ g = Sum.map g g

map : {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
      P ⇒ Q → SymClosure P ⇒ SymClosure Q
map = gmap id

------------------------------------------------------------------------
-- Properties

-- Symmetric closures are symmetric.
symmetric : (_∼_ : Rel A ℓ) → Symmetric (SymClosure _∼_)
symmetric _ (fwd a∼b) = bwd a∼b
symmetric _ (bwd b∼a) = fwd b∼a


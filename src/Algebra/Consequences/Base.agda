------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core using (Op₁; Op₂)
import Algebra.Definitions as Definitions
  using (Congruent₂; LeftCongruent; RightCongruent
        ; Selective; Idempotent; SelfInverse; Involutive)
open import Data.Sum.Base using (_⊎_; reduce)
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive)

module Congruence {ℓ} {_∙_ : Op₂ A} (_≈_ : Rel A ℓ) (open Definitions _≈_)
                  (cong : Congruent₂ _∙_) (refl : Reflexive _≈_)
  where

  ∙-congˡ : LeftCongruent _∙_
  ∙-congˡ {x} = mono₂⇒monoˡ _ _≈_ _≈_ (refl {x = x}) cong x

  ∙-congʳ : RightCongruent _∙_
  ∙-congʳ {x} = mono₂⇒monoʳ _≈_ _ _≈_ (refl {x = x}) cong x

module _ {ℓ} {_∙_ : Op₂ A} (_≈_ : Rel A ℓ) (open Definitions _≈_) where

  sel⇒idem : Selective _∙_ → Idempotent _∙_
  sel⇒idem sel x = reduce (sel x x)

module _ {ℓ} {f : Op₁ A} (_≈_ : Rel A ℓ) (open Definitions _≈_) where

  reflexive∧selfInverse⇒involutive : Reflexive _≈_ →
                                     SelfInverse f →
                                     Involutive f
  reflexive∧selfInverse⇒involutive refl inv _ = inv refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

reflexive+selfInverse⇒involutive = reflexive∧selfInverse⇒involutive
{-# WARNING_ON_USAGE reflexive+selfInverse⇒involutive
"Warning: reflexive+selfInverse⇒involutive was deprecated in v2.0.
Please use reflexive∧selfInverse⇒involutive instead."
#-}

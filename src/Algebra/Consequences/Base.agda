------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core
open import Algebra.Definitions
open import Data.Sum.Base
open import Relation.Binary.Core
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ)
open import Relation.Binary.Definitions using (Reflexive)

module _ {ℓ} {_∙_ : Op₂ A} (_≈_ : Rel A ℓ) where

  sel⇒idem : Selective _≈_ _∙_ → Idempotent _≈_ _∙_
  sel⇒idem sel x = reduce (sel x x)

  module Congruence (cong : Congruent₂ _≈_ _∙_) (refl : Reflexive _≈_) where

    congˡ : LeftCongruent _≈_ _∙_
    congˡ = mono₂⇒monoˡ {≤₁ = _≈_} {≤₂ = _≈_} {≤₃ = _≈_} refl cong

    congʳ : RightCongruent _≈_ _∙_
    congʳ = mono₂⇒monoʳ {≤₁ = _≈_} {≤₂ = _≈_} {≤₃ = _≈_} refl cong

module _ {ℓ} {f : Op₁ A} (_≈_ : Rel A ℓ) where

  reflexive∧selfInverse⇒involutive : Reflexive _≈_ →
                                     SelfInverse _≈_ f →
                                     Involutive _≈_ f
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

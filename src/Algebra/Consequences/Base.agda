------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Consequences.Base
  {a} {A : Set a} where

open import Algebra.Core
open import Algebra.Definitions
open import Data.Sum.Base
open import Relation.Binary.Core
open import Relation.Binary.Definitions using (Reflexive)

module _ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) where

  sel⇒idem : Selective _≈_ _•_ → Idempotent _≈_ _•_
  sel⇒idem sel x with sel x x
  ... | inj₁ x•x≈x = x•x≈x
  ... | inj₂ x•x≈x = x•x≈x

module _ {ℓ} {f : Op₁ A} (_≈_ : Rel A ℓ) where

  reflexive+selfinverse⇒involutive : Reflexive _≈_ →
                                     SelfInverse _≈_ f →
                                     Involutive _≈_ f
  reflexive+selfinverse⇒involutive refl inv _ = inv refl


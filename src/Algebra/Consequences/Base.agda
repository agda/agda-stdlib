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
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

private
  variable
    x y : A

module _ {ℓ} {_•_ : Op₂ A} (_≈_ : Rel A ℓ) where

  sel⇒idem : Selective _≈_ _•_ → Idempotent _≈_ _•_
  sel⇒idem sel x = reduce (sel x x)

module _ {ℓ} {f : Op₁ A} (_≈_ : Rel A ℓ) where

  reflexive∧selfInverse⇒involutive : Reflexive _≈_ →
                                     SelfInverse _≈_ f →
                                     Involutive _≈_ f
  reflexive∧selfInverse⇒involutive refl inv _ = inv refl

module _ {ℓ} {_∙_ : Op₂ A} {0# 1# : A} (_≈_ : Rel A ℓ) where

  private
    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

  integral⇒noZeroDivisors : Integral _≈_ 1# 0# _∙_ → 1# ≉ 0# →
                            NoZeroDivisors _≈_ 0# _∙_
  integral⇒noZeroDivisors (inj₁ trivial)        = contradiction trivial
  integral⇒noZeroDivisors (inj₂ noZeroDivisors) = λ _ → noZeroDivisors

module _ {ℓ} {_∙_ : Op₂ A} {0# : A} (_≈_ : Rel A ℓ) where

  private
    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

  noZeroDivisors⇒x≉0∧y≉0⇒xẏ≉0 : NoZeroDivisors _≈_ 0# _∙_ →
                                x ≉ 0# → y ≉ 0# → (x ∙ y) ≉ 0#
  noZeroDivisors⇒x≉0∧y≉0⇒xẏ≉0 noZeroDivisors x≉0 y≉0 xy≈0 with noZeroDivisors xy≈0
  ... | inj₁ x≈0 = x≉0 x≈0
  ... | inj₂ y≈0 = y≉0 y≈0


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
